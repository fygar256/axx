#!/usr/bin/env python3
"""axx: a general-purpose, pattern-file-driven assembler.

Unlike a conventional assembler that hardcodes one instruction set, axx reads
an instruction-set description (a ".axx" pattern file) that maps mnemonic
syntax to binary encodings, and applies it to an assembly source file. This
lets the same engine target arbitrary ISAs (x86_64, ARM64, Z80, VLIW/EPIC
architectures, ...) just by swapping the pattern file.

High-level pipeline (see Assembler.run() near the bottom of this file):
  1. Read and parse the pattern file (PatternFileReader) into a list of
     pattern entries (mnemonic template -> encoding expression, plus
     directives like .setsym/.bits/.vliw that configure the assembler).
  2. Pass 1: run the source through the pattern matcher repeatedly
     ("relaxation") until label addresses stop changing, so that
     variable-length instructions (e.g. short vs. near jumps) converge to
     their final size.
  3. Pass 2: re-run the source one final time with addresses now known,
     emitting the actual object bytes and (if requested) ELF64 relocatable
     object output, DWARF line-number info, and an export/import label file
     for splitting a program across multiple invocations.

Sections are tracked as a sequence of (name, start_pc, length) fragments
rather than one contiguous range per name, because a source file can leave a
section and re-enter it later (e.g. .text -> .data -> .text); the true
section-relative position of anything defined in a later fragment must
account for the other sections interleaved before it.
"""


from decimal import Decimal, localcontext
try:
    import readline  # noqa: F401  (side effect: line editing for input())
except ImportError:
    pass
import ast
import functools
import itertools
import struct
import sys
import os
import math
import re
import tempfile
import uuid


# Marks the "no previous relaxation pass yet" state, distinct from any real
# label-address snapshot (which is always a plain dict), so the first Pass 1
# iteration can be told apart from later ones without a separate flag.
_RELAXATION_SENTINEL = object()


EXP_PAT = 0
EXP_ASM = 1
exp_typ = 'i'


# Placeholder characters standing in for the pattern-file bracket escapes
# "[[" / "]]" once they've been substituted out of a line, so the rest of the
# parser can treat them as ordinary single characters instead of two-char
# sequences.
OB = chr(0x90)
CB = chr(0x91)


# UNDEF is deliberately an enormous (but finite) integer rather than None/NaN:
# label values flow through ordinary arithmetic (label+4, label-$$, etc.), and
# using a real integer lets "undefined" propagate through +,-,*,... without
# every call site having to special-case a non-numeric sentinel. Any
# real-world label/expression value should stay far below
# _UNDEF_DERIVED_THRESHOLD, so a result that lands at or above it is treated
# as "derived from an undefined value" (see _is_undef_derived below).
UNDEF = (1 << 1024) - 1
VAR_UNDEF = 0

_UNDEF_DERIVED_THRESHOLD = 1 << 768


# Below this, a huge value is assumed to be legitimate (e.g. a 256-bit
# constant); at/above it we start treating it as UNDEF-derived. The gap
# between the two thresholds is just a buffer so the one-time warning below
# fires before a value could plausibly reach _UNDEF_DERIVED_THRESHOLD.
_UNDEF_SANE_CEILING = 1 << 256
_undef_ceiling_warned = False


def _is_undef_derived(v):
    """True if v is UNDEF itself, or so large it must have propagated from
    an UNDEF value through arithmetic (e.g. UNDEF - 4). Warns once (not per
    occurrence) if a value is large enough to be suspicious but still below
    the derived-from-UNDEF threshold, since that could mean a real huge
    constant is about to be misclassified."""
    global _undef_ceiling_warned
    if v == UNDEF:
        return True
    if isinstance(v, int):
        av = abs(v)
        if _UNDEF_SANE_CEILING <= av < _UNDEF_DERIVED_THRESHOLD and not _undef_ceiling_warned:
            _undef_ceiling_warned = True
            print(" warning - a value larger than 2**256 was computed; the UNDEF-sentinel "
                  "heuristic may misclassify very large legitimate values as undefined.",
                  file=sys.stderr)
        return av >= _UNDEF_DERIVED_THRESHOLD
    return False


@functools.lru_cache(maxsize=None)
def _lead_caps(pat_text):
    """Cheap prefilter: extract a pattern's leading run of literal capital
    letters (skipping spaces) so obviously-mismatched patterns can be
    skipped before paying for full match0() (which is combinatorial in
    the number of optional groups). Pattern text is immutable once the
    pattern file is read, so results are memoized."""
    p = []
    for ch in pat_text:
        if ch in CAPITAL:
            p.append(ch)
        elif ch == ' ':
            continue
        else:
            break
    return ''.join(p)


CAPITAL = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
LOWER = "abcdefghijklmnopqrstuvwxyz"
DIGIT = '0123456789'
XDIGIT = "0123456789ABCDEF"
ALPHABET = LOWER + CAPITAL


ERRORS = [
    "",
    "Invalid syntax.",
    "Address out of range.",
    "Value out of range.",
    "",
    "Register out of range.",
    "Port number out of range."
]


# ELF e_machine relocation-numbering tables: everything this assembler needs
# to emit correct ELF32/ELF64 relocatable objects for one target
# architecture, keyed by e_machine number and selected via `-m`/`--machine`.
#
# `width_guess` {encoded-field-byte-width: reloc type} picks a relocation
# type from an auto-detected label reference with no explicit `::reloctype`
# override, mirroring real assemblers' convention that a field the same
# width as a native call/jmp displacement (traditionally 4 bytes, even on
# 64-bit targets) most likely IS one, while other widths most likely hold an
# absolute address/data reference -- this convention is deliberately kept
# per-architecture rather than derived, since it encodes "the common case for
# this width on this ISA", not a fact about the relocation numbers.
#
# `pc_rel` is the set of relocation-type numbers that are PC-relative (vs.
# absolute) for this machine, consulted when deciding the addend formula.
#
# `named` is `{symbolic name usable in a "::name" override: (reloc type,
# expected encoded field byte width)}` -- the single source of truth for
# `.EXTERN`/`.EQU`/the `-i` import-file syntax's `::reloctype` overrides
# *and* the reverse lookup `-E` export uses to print a symbolic name; the
# per-name width is what `::reloctype`'s field-width sanity check
# (`_elf_machine_reloc_bytes`) validates an override against, so it can never
# drift out of sync with that check the way three independently-maintained
# copies of the same table previously could (see git history/prior audits).
#
# `extern_default` is the relocation type a bare `.EXTERN label` (no
# `::reloctype`) gets. `dwarf_abs` is the relocation type representing an
# absolute native-pointer-width address, used for DWARF `.debug_info`/
# `.debug_line` address relocations (`-g`); DWARF generation on a 32-bit
# target is not yet implemented (see `_build_dwarf_sections`) so this is
# presently only consulted for `elfclass == 2` machines.
#
# Confidence note: x86_64(62)/i386(3)/ARM(40)/AArch64(183)/PowerPC(20)/
# RISC-V(243) reproduce this assembler's original, already-in-use numbering
# exactly (a handful of small additions -- e.g. i386's real R_386_PC16=21 --
# were made only where needed so a new `::name` override resolves to a
# working relocation; nothing an existing pattern file already relied on was
# renumbered). The remaining architectures (PowerPC64, S/390(x), SPARCV9,
# SuperH, M68K) are new and use well-established psABI relocation numbers
# from documentation, cross-checked where possible (i386's numbers were
# verified against a real `gcc -m32`-produced object file); none of them
# have been exercised against a real cross-linker for these architectures,
# so treat them as "best effort, structurally valid" rather than
# field-proven, and report back any discrepancy found in practice.
#
# `is_rela` says whether this machine's psABI stores relocation addends
# explicitly (RELA: a separate addend field per entry, `.rela.NAME`
# sections, SHT_RELA) or implicitly (REL: no addend field at all --
# `.rel.NAME` sections, SHT_REL -- the addend instead lives baked directly
# into the relocated field's bytes, and the linker reads-modifies-writes
# it). This matters at the byte level, not just the section name: for a REL
# machine, `write_elf_obj` must patch the *already-encoded* field bytes to
# hold the addend value that would otherwise have gone in RELA's addend
# field, since nothing else will ever record that value once the .o is
# written (see `write_elf_obj`'s REL patching pass). i386's REL convention
# was confirmed against a real `gcc -m32`-produced object earlier in this
# file's development. The rest are this assembler's best-effort read of
# publicly documented psABI conventions, similarly unverified against a
# real cross-linker -- flag any that turn out wrong.
_ELF_MACHINE_RAW = {
    3: dict(     # EM_386 (i386)
        name='i386', elfclass=1, is_rela=False,   # confirmed via `gcc -m32`
        width_guess={4: 2, 2: 20, 1: 22},
        pc_rel={2, 13, 21, 23},
        extern_default=2,
        named={
            'abs32': (1, 4), 'pc32': (2, 4), 'rel32': (2, 4),
            'got32': (3, 4), 'plt32': (4, 4),
            'gotoff': (9, 4), 'gotpc': (10, 4),
            'abs16': (20, 2), 'pc16': (21, 2),
            'abs8': (22, 1), 'pc8': (23, 1),
        },
        dwarf_abs=1,
    ),
    4: dict(     # EM_68K (M68K)
        name='m68k', elfclass=1, is_rela=True,
        width_guess={4: 4, 2: 2, 1: 3},
        pc_rel={4, 5, 6},
        extern_default=4,
        named={
            'abs32': (1, 4), 'abs16': (2, 2), 'abs8': (3, 1),
            'pc32': (4, 4), 'rel32': (4, 4),
            'pc16': (5, 2), 'pc8': (6, 1),
        },
        dwarf_abs=1,
    ),
    20: dict(    # EM_PPC (PowerPC 32-bit)
        name='PowerPC', elfclass=1, is_rela=True,
        width_guess={4: 26, 2: 4},
        pc_rel={10, 26},
        extern_default=26,
        named={
            'abs32': (1, 4), 'abs16': (3, 2), 'abs16lo': (4, 2),
            'abs16hi': (5, 2), 'abs16ha': (6, 2),
            'pc32': (26, 4), 'rel32': (26, 4),
            'pc24': (10, 4), 'rel24': (10, 4),
        },
        dwarf_abs=1,
    ),
    21: dict(    # EM_PPC64
        name='PowerPC64', elfclass=2, is_rela=True,
        width_guess={8: 38, 4: 26, 2: 4},
        pc_rel={10, 26, 44},
        extern_default=26,
        named={
            'abs64': (38, 8), 'abs32': (1, 4),
            'abs16': (3, 2), 'abs16lo': (4, 2),
            'abs16hi': (5, 2), 'abs16ha': (6, 2),
            'pc64': (44, 8), 'rel64': (44, 8),
            'pc32': (26, 4), 'rel32': (26, 4),
            'pc24': (10, 4), 'rel24': (10, 4),
        },
        dwarf_abs=38,
    ),
    22: dict(    # EM_S390 (s390x)
        name='s390x', elfclass=2, is_rela=True,
        width_guess={8: 22, 4: 5, 2: 3, 1: 1},
        pc_rel={5, 16, 23},
        extern_default=5,
        named={
            'abs64': (22, 8), 'abs32': (4, 4), 'abs16': (3, 2), 'abs8': (1, 1),
            'pc64': (23, 8), 'pc32': (5, 4), 'rel32': (5, 4), 'pc16': (16, 2),
        },
        dwarf_abs=22,
    ),
    40: dict(    # EM_ARM (32-bit)
        name='ARM', elfclass=1, is_rela=False,
        width_guess={4: 3, 2: 4, 1: 8},
        pc_rel={1, 3},
        extern_default=3,
        named={
            'abs32': (2, 4), 'pc24': (1, 4),
            'pc32': (3, 4), 'rel32': (3, 4),
            'abs16': (5, 2), 'abs12': (6, 4), 'abs8': (8, 1),
        },
        dwarf_abs=2,
    ),
    42: dict(    # EM_SH (SuperH)
        name='SuperH', elfclass=1, is_rela=True,
        width_guess={4: 2},
        pc_rel={2},
        extern_default=2,
        named={'abs32': (1, 4), 'pc32': (2, 4), 'rel32': (2, 4)},
        dwarf_abs=1,
    ),
    43: dict(    # EM_SPARCV9
        name='SPARCV9', elfclass=2, is_rela=True,
        width_guess={8: 32, 4: 6, 2: 2, 1: 1},
        pc_rel={4, 5, 6, 46},
        extern_default=6,
        named={
            'abs64': (32, 8), 'abs32': (3, 4), 'abs16': (2, 2), 'abs8': (1, 1),
            'pc64': (46, 8), 'rel64': (46, 8),
            'pc32': (6, 4), 'rel32': (6, 4),
            'pc16': (5, 2), 'pc8': (4, 1),
        },
        dwarf_abs=32,
    ),
    62: dict(    # EM_X86_64
        name='x86-64', elfclass=2, is_rela=True,
        width_guess={8: 1, 4: 2, 2: 12, 1: 14},
        pc_rel={2, 4, 9, 13, 15, 24},
        extern_default=2,
        named={
            'abs64': (1, 8), 'abs32': (10, 4), 'abs32s': (11, 4),
            'abs16': (12, 2), 'abs8': (14, 1),
            'pc32': (2, 4), 'rel32': (2, 4), 'plt32': (4, 4),
            'pc16': (13, 2), 'pc8': (15, 1), 'pc64': (24, 8),
            'got32': (3, 4), 'gotpcrel': (9, 4), 'got64': (27, 8),
        },
        dwarf_abs=1,
    ),
    183: dict(   # EM_AARCH64
        name='AArch64', elfclass=2, is_rela=True,
        width_guess={8: 257, 4: 261, 2: 262},
        pc_rel={260, 261, 262},
        extern_default=261,
        named={
            'abs64': (257, 8), 'abs32': (258, 4), 'abs16': (259, 2),
            'pc64': (260, 8), 'rel64': (260, 8),
            'pc32': (261, 4), 'rel32': (261, 4),
            'pc16': (262, 2), 'rel16': (262, 2),
        },
        dwarf_abs=257,
    ),
    243: dict(   # EM_RISCV (RV64)
        name='RISC-V', elfclass=2, is_rela=True,
        width_guess={8: 2, 4: 1, 2: 34, 1: 33},
        pc_rel=set(),
        extern_default=1,
        named={
            # abs16/abs8 (34/33) reproduce this assembler's pre-existing
            # width-guess numbering as-is; unlike the other entries in this
            # table they are not independently confirmed against psABI
            # documentation (RISC-V's base spec does not define a plain
            # absolute 16-/8-bit relocation the way most other ISAs do), so
            # treat those two specifically as low-confidence.
            'abs64': (2, 8), 'abs32': (1, 4), 'abs16': (34, 2), 'abs8': (33, 1),
        },
        dwarf_abs=2,
    ),
}


def _build_elf_machine_tables(raw):
    """Expand `_ELF_MACHINE_RAW`'s `named` dict of `{name: (reloc_type,
    width)}` into the two derived views the rest of the assembler actually
    looks up by: a plain `{name: reloc_type}` map for parsing a `::name`
    override, and its reverse `{reloc_type: name}` for `-E` export, plus
    `reloc_bytes` = `{reloc_type: width}` for validating an override against
    the field it's attached to. Deriving all three from one source (instead
    of maintaining them as separate hand-written tables, as this file used
    to) means they can't independently drift out of sync."""
    out = {}
    for machine, entry in raw.items():
        named_types = {name: rt for name, (rt, _w) in entry['named'].items()}
        reloc_bytes = {rt: w for (rt, w) in entry['named'].values()}
        reverse = {}
        for name, rt in named_types.items():
            reverse.setdefault(rt, name)
        out[machine] = dict(entry,
                             named=named_types,
                             reloc_bytes=reloc_bytes,
                             reverse=reverse)
    return out


ELF_MACHINES = _build_elf_machine_tables(_ELF_MACHINE_RAW)


class VLIWState:
    """Configuration and in-progress state for VLIW/EPIC-style instruction
    packing, set up by the pattern file's .vliw directive and consumed while
    assembling one "!!"-separated slot group into a single fixed-width
    packet (see VLIWProcessor.vliwprocess())."""

    def __init__(self):
        self.instbits = 41       # bit width of one instruction slot within a packet
        self.nop = []            # filler bytes used to pad an under-full packet
        self.bits = 128          # total packet width in bits
        self.slotset = []        # valid slot-count -> template-bits mappings from .vliw
        self.flag = False        # True once a .vliw directive has configured VLIW mode
        self.templatebits = 0x00 # width of the packet's template/opcode field
        self.stop = 0            # set when "!!!!" (end-of-packet marker) is seen
        self.cnt = 1


class ElfState:
    """ELF64 relocatable object-file output state: what to write, and the
    bookkeeping needed to notice "this instruction's operand is actually a
    label reference" while Pass 2 emits object bytes, so a relocation entry
    can be generated for it instead of (or in addition to) a resolved value."""

    def __init__(self):
        self.osabi: int = 9      # ELF e_ident[EI_OSABI]; default 9 = FreeBSD
        self.objfile: str = ""
        self.machine: int = 62   # ELF e_machine; default 62 = EM_X86_64

        self.relocations = []
        self.tracking = False    # True only during Pass 2 while writing an ELF object
        self.label_refs_seen = []
        self.current_word_idx: int = -1  # index within the current instruction's
                                          # object-code words that a label reference
                                          # was seen at; -1 means "not inside makeobj()"
        self.var_to_label: dict = {}     # captured pattern variable -> (label name, value),
                                          # used to recover which label a !x-style
                                          # capture came from when emitting relocations
        self.capturing_var: str | None = None  # pattern variable currently being
                                                # captured, if any

        self.gen_debug: bool = False  # -g flag: also emit DWARF line-number info
        self.line_map: list = []

        # {encoded-field-byte-width: reloc type}, set from the source file's
        # `.reloctype` directive. Overrides ELF_MACHINES[machine]['width_guess']
        # on a per-width basis for auto-detected (no explicit ::reloctype)
        # label references; see AssemblyDirectiveProcessor.reloctype_processing
        # and its use at the width_guess lookup in ObjectGenerator.makeobj().
        self.reloctype_override: dict = {}


class RelaxationState:
    """State specific to the Pass 1 relaxation loop, which re-assembles the
    source repeatedly until label addresses stop moving (see Assembler.run()).
    Kept separate from AssemblerState mainly for readability; relaxation is a
    Pass 1-only concern."""

    def __init__(self):
        self.pas = 0  # 0 = interactive/single-line mode, 1 = Pass 1, 2 = Pass 2

        # Size-probe mode: while true, an undefined forward-reference label
        # resolves to 0 instead of erroring, purely so a pattern's encoded
        # size can be estimated before the label is known.
        self.pass1_size_mode = False

        # Snapshot of each label's resolved address from the previous
        # relaxation iteration. Sentinel value on the very first iteration
        # (see _RELAXATION_SENTINEL) so forward references have no estimate
        # yet and must fall back to 0-sized/UNDEF handling instead.
        self.pass1_prev_label_pcs = _RELAXATION_SENTINEL

        # Per-label snapshot of the same address across iterations, used so
        # a still-forward-referenced label can be estimated using its value
        # from the previous pass (letting variable-length encodings converge)
        # rather than being flatly undefined mid-relaxation.
        self.relax_prev_values = {}

        # Which (file, line) pairs have already been warned about exhausting
        # the pattern-matching combination budget, so the warning fires once
        # per site instead of once per relaxation iteration.
        self.combo_budget_warned = set()


class AssemblerState:
    """The assembler's central mutable state ("God object"), shared by every
    other class in this file (LabelManager, ExpressionEvaluator, the various
    directive processors, etc.) via a single `state` reference each holds.

    VLIWState/ElfState/RelaxationState hold logically-grouped subsets of this
    state, but old code (and this file's many call sites) was written
    expecting flat attributes like `state.vliwbits` or `state.pas` directly
    on AssemblerState. `_FORWARDED_ATTRS` plus `__getattr__`/`__setattr__`
    below transparently forward those flat names to the grouped sub-objects,
    so both styles work without duplicating any data.
    """

    def __init__(self):

        self.outfile = ""
        self.expfile = ""       # -e: plain-text label export path
        self.expfile_elf = ""   # -E: ELF-flavored label export path
        self.impfile = ""       # -i: label import path (for split builds)

        self.pc = 0        # current raw, monotonically-increasing program counter
        self.padding = 0   # fill byte used by .ORG when advancing pc

        # $$ / $. support: pc at the start / end of the instruction currently
        # being encoded, and whether we're inside that encoding at all. Only
        # meaningful while _in_binary_list is True (see ExpressionEvaluator
        # factor() handling of "$$"/"$.").
        self.pc_instr_start = 0
        self.pc_instr_end = 0
        self._in_binary_list = False

        self.lwordchars = DIGIT + ALPHABET + "_."             # valid label-name characters
        self.swordchars = DIGIT + ALPHABET + "_%$-~&|"         # valid .setsym-symbol characters

        self.current_section = ".text"
        self.current_file = ""

        self.labels = {}          # name -> [value, section, is_equ, is_imported, reloc_type?]
        self.sections = {}        # name -> [start_pc, cumulative_size, entry_pc, confirmed]
                                   # (of the section's *current* open visit; see
                                   # section_ranges below for the full fragment history)
        self.symbols = {}         # pattern-file .setsym symbols currently in scope
        self.patsymbols = {}      # baseline .setsym symbols as defined by the pattern
                                   # file itself, restored at the top of every line
        self.export_labels = {}   # subset of labels to write via -e/-E
        self.pat = []              # parsed pattern-file entries (PatternFileReader output)

        self.vliw = VLIWState()

        self.expmode = EXP_PAT
        self.error_undefined_label = False
        self.error_label_conflict = False

        # Persistent (never auto-reset per-line, unlike error_undefined_label/
        # error_label_conflict above): set once and left set for the rest of
        # the run whenever a user-facing " error - ..." is actually reported
        # during assembly. run() checks this after Pass 2 to refuse to write
        # output for a build that printed errors, instead of silently
        # succeeding with incomplete/wrong bytes.
        self.had_error = False

        # True while PatternMatcher is trying a candidate pattern that hasn't
        # been chosen yet; suppresses "undefined label" errors for references
        # that only exist because of a not-yet-rejected trial match.
        self._in_match_attempt = False

        self.align = 16
        self.bts = 8              # bits per "word" (the pattern file's basic addressable unit)
        self.endian = 'little'
        self.byte = 'yes'
        self.debug = False

        self.cl = ""
        self.ln = 0
        self.fnstack = []   # .INCLUDE call stack: saved current_file per nesting level
        self.lnstack = []   # .INCLUDE call stack: saved line number per nesting level

        self.vars = [VAR_UNDEF for i in range(26)]  # pattern !a-!z capture variables

        self.deb1 = ""
        self.deb2 = ""

        self.exp_typ: str = 'i'

        self.relax = RelaxationState()

        self.verbose: bool = False

        # Temp file backing a "stdin" pseudo-include (see fileassemble()):
        # created on first use, reused across relaxation iterations, deleted
        # in run()'s cleanup.
        self.stdin_tmp_path: str | None = None

        self.elf = ElfState()

        self.init_func: str | None = None
        self.fini_func: str | None = None

        # Per-pattern-check state used by the pattern file's .check/.clrcheck
        # directives (operand-combination validation during matching).
        self.check_constraints: dict = {}

        # Chronological (section_name, start_pc, length) fragments recording
        # every visit to every section, in visitation order. A section
        # entered more than once (.text -> .data -> .text) has one entry per
        # visit here, which is what makes it possible to reconstruct its true
        # (non-contiguous-in-pc-space) byte layout in the final output; see
        # _section_word_ranges()/_addr_to_word_offset() below.
        self.section_ranges: list = []

        # Set of section names touched while evaluating a reloc_type-less
        # .EQU expression; None when not currently inside one. Used to warn
        # if the expression silently assumes a fixed relative layout between
        # sections (see AssemblyDirectiveProcessor.label_processing()).
        self._equ_sections_touched = None

    def should_report_errors(self):
        """Whether user-facing errors should be printed right now: only in
        interactive/single-line mode (pas==0) or the final Pass 2 (pas==2),
        never during Pass 1 relaxation where a "forward reference" is often
        just not resolved *yet*, not actually invalid."""
        return self.pas == 2 or self.pas == 0

    # Flat legacy attribute name -> (sub-object attr, sub-object field) map
    # consumed by __getattr__/__setattr__ below, so `state.vliwbits` reads
    # and writes `state.vliw.bits` transparently.
    _FORWARDED_ATTRS = {
        'pas':                   ('relax', 'pas'),
        '_pass1_size_mode':      ('relax', 'pass1_size_mode'),
        '_pass1_prev_label_pcs': ('relax', 'pass1_prev_label_pcs'),
        '_relax_prev_values':    ('relax', 'relax_prev_values'),
        '_combo_budget_warned':  ('relax', 'combo_budget_warned'),

        'vliwinstbits':     ('vliw', 'instbits'),
        'vliwnop':          ('vliw', 'nop'),
        'vliwbits':         ('vliw', 'bits'),
        'vliwset':          ('vliw', 'slotset'),
        'vliwflag':         ('vliw', 'flag'),
        'vliwtemplatebits': ('vliw', 'templatebits'),
        'vliwstop':         ('vliw', 'stop'),
        'vcnt':             ('vliw', 'cnt'),

        'osabi':                  ('elf', 'osabi'),
        'elf_objfile':            ('elf', 'objfile'),
        'elf_machine':            ('elf', 'machine'),
        'relocations':            ('elf', 'relocations'),
        '_elf_tracking':          ('elf', 'tracking'),
        '_elf_label_refs_seen':   ('elf', 'label_refs_seen'),
        '_elf_current_word_idx':  ('elf', 'current_word_idx'),
        '_elf_var_to_label':      ('elf', 'var_to_label'),
        '_elf_capturing_var':     ('elf', 'capturing_var'),
        'gen_debug':              ('elf', 'gen_debug'),
        'line_map':               ('elf', 'line_map'),
        'reloctype_override':     ('elf', 'reloctype_override'),
    }
    # Build one `property` per entry in _FORWARDED_ATTRS and inject it into
    # this class body (this loop runs once, at class-definition time, not
    # per instance). _sub_name/_sub_attr are bound as default arguments
    # rather than captured by reference, since a plain closure over the loop
    # variables would make every generated property forward to whatever
    # (_sub_name, _sub_attr) happened to be *last* in the dict.
    for _old_name, (_sub_name, _sub_attr) in _FORWARDED_ATTRS.items():
        def _make_forward(_sub_name=_sub_name, _sub_attr=_sub_attr):
            def _getter(self):
                return getattr(getattr(self, _sub_name), _sub_attr)

            def _setter(self, value):
                setattr(getattr(self, _sub_name), _sub_attr, value)
            return property(_getter, _setter)
        locals()[_old_name] = _make_forward()
    # Clean up the loop/helper names so they don't themselves become
    # unintended class attributes.
    del _old_name, _sub_name, _sub_attr, _make_forward


class StringUtils:
    """Stateless string/line-parsing helpers shared by the pattern-file and
    source-file tokenizers. Static methods only: none of this depends on
    assembler state."""

    # a-z -> A-Z only; str.upper() would also touch non-ASCII (e.g. 'ß'->'SS'),
    # which this deliberately does not.
    _ASCII_UPPER = str.maketrans(LOWER, CAPITAL)

    @staticmethod
    def upper(s):
        """Uppercase only ASCII lowercase letters, leaving everything else
        (digits, punctuation, non-ASCII) untouched."""
        return s.translate(StringUtils._ASCII_UPPER)

    @staticmethod
    def q(s, t, idx):
        """Case-insensitive "does s at idx start with t" check."""
        return StringUtils.upper(s[idx:idx + len(t)]) == StringUtils.upper(t)

    @staticmethod
    def skipspc(s, idx):
        while idx < len(s) and s[idx] in ' \t':
            idx += 1
        return idx

    @staticmethod
    def skip_squote_literal(s, i):
        """Given i pointing at a single-quote that opens a character literal
        ('a', '\\n', '\\x41', ...), return the index just past its closing
        quote, so remove_comment_asm() doesn't mistake a quoted ';' for a
        comment start. Falls back to i+1 (treat as a lone quote, not a
        literal) if the quote never closes."""
        j = i + 1
        if j < len(s) and s[j] == '\\' and j + 1 < len(s):
            esc_char = s[j + 1]
            if esc_char in 'xX':
                k = j + 2
                hex_digits = 0
                while k < len(s) and s[k] in '0123456789abcdefABCDEF' and hex_digits < 2:
                    k += 1
                    hex_digits += 1
                if k < len(s) and s[k] == '\'':
                    return k + 1
            elif j + 2 < len(s) and s[j + 2] == '\'':
                return j + 3
        elif j < len(s) and j + 1 < len(s) and s[j + 1] == '\'':
            return j + 2
        return i + 1

    @staticmethod
    def parse_hex_char_literal(s, idx):
        """Parse a C-style '\\xHH' character literal (1-2 hex digits)
        starting at idx (pointing at the opening quote). Mirrors the
        \\x-escape branch of skip_squote_literal() above, which already
        recognizes this form well enough to not mistake a quoted ';' for a
        comment -- but ExpressionEvaluator.factor1() had no matching case to
        actually evaluate one, so e.g. "MOV '\\x41'" (equivalent to "MOV 'A'")
        failed with a syntax error. Returns (True, value, new_idx) on
        success, or (False, 0, idx) unchanged if this isn't a well-formed
        \\x literal, so the caller can fall through to other literal forms."""
        if not (idx + 3 <= len(s) and s[idx] == "'" and s[idx + 1] == '\\'
                and s[idx + 2] in 'xX'):
            return False, 0, idx
        j = idx + 3
        hex_digits = ''
        while j < len(s) and s[j] in '0123456789abcdefABCDEF' and len(hex_digits) < 2:
            hex_digits += s[j]
            j += 1
        if hex_digits and j < len(s) and s[j] == "'":
            return True, int(hex_digits, 16), j + 1
        return False, 0, idx

    _SPACE_RUNS = re.compile(r'\s{2,}')

    @staticmethod
    def reduce_spaces(text):
        """Collapse runs of whitespace to a single space."""
        return StringUtils._SPACE_RUNS.sub(' ', text)

    @staticmethod
    def remove_comment(l):
        """Strip a pattern-file /* ... */ (line-oriented: only the opening
        marker matters here, the rest of the line is discarded)."""
        idx = 0
        while idx < len(l):
            if l[idx:idx + 2] == '/*':
                return "" if idx == 0 else l[0:idx]
            idx += 1
        return l

    @staticmethod
    def remove_comment_asm(l):
        """Strip a source-line ';' comment, but only outside string/char
        literals: a ';' inside "..." or a 'x' character literal is real
        content, not a comment start. Tracks double-quote state directly and
        delegates single-quote literals to skip_squote_literal() since those
        can contain escapes (\\x41) that a naive quote-toggle would misparse."""
        in_dquote = False
        i = 0
        while i < len(l):
            ch = l[i]

            if ch == '\\' and in_dquote:
                if i + 1 < len(l):
                    i += 2
                else:
                    i += 1
                continue

            if ch == '"':
                in_dquote = not in_dquote
            elif ch == '\'' and not in_dquote:
                i = StringUtils.skip_squote_literal(l, i)
                continue
            elif ch == ';' and not in_dquote:
                return l[:i].rstrip()

            i += 1
        if in_dquote:
            print(f" warning - unterminated string literal in line: {l!r}", file=sys.stderr)
        return l.rstrip()

    @staticmethod
    def get_param_to_spc(s, idx):
        """Read one whitespace-delimited token, stopping early at a "!!"
        VLIW slot separator so a token never accidentally swallows the next
        slot's content."""
        t = ""
        idx = StringUtils.skipspc(s, idx)
        while idx < len(s) and s[idx] != ' ' and s[idx:idx + 2] != '!!':
            t += s[idx]
            idx += 1
        return t, idx

    @staticmethod
    def get_param_to_eon(s, idx):
        """Read the rest of the line (spaces included), stopping at a "!!"
        VLIW slot separator."""
        t = ""
        idx = StringUtils.skipspc(s, idx)
        while idx < len(s) and s[idx:idx + 2] != '!!':
            t += s[idx]
            idx += 1
        return t, idx

    @staticmethod
    def get_string(l2):
        """Parse a double-quoted string literal (as used by .ascii/.asciz
        and string-mode search/replace), applying C-style backslash escapes:
        \\n \\t \\r \\" \\\\, \\xHH (1-2 hex digits), \\uHHHH / \\UHHHHHHHH.
        Returns "" if l2 doesn't start with a '"' at all."""
        idx = 0
        idx = StringUtils.skipspc(l2, idx)
        if l2 == '' or idx >= len(l2) or l2[idx] != '"':
            return ""
        idx += 1
        s = ""
        while idx < len(l2):
            if l2[idx] == '\\' and idx + 1 < len(l2):
                next_char = l2[idx + 1]
                if next_char == '"':
                    s += '"'
                    idx += 2
                elif next_char == '\\':
                    s += '\\'
                    idx += 2
                elif next_char == 'n':
                    s += '\n'
                    idx += 2
                elif next_char == 't':
                    s += '\t'
                    idx += 2
                elif next_char == 'r':
                    s += '\r'
                    idx += 2
                elif next_char in 'xX':
                    idx += 2
                    hex_str = ''
                    while idx < len(l2) and l2[idx] in '0123456789abcdefABCDEF' and len(hex_str) < 2:
                        hex_str += l2[idx]
                        idx += 1
                    if idx < len(l2) and l2[idx] in '0123456789abcdefABCDEF':
                        print(f" warning - '\\x' escape takes at most 2 hex digits; "
                              f"extra digit(s) treated as literal characters in: {l2!r}", file=sys.stderr)
                    if hex_str:
                        s += chr(int(hex_str, 16))
                    else:
                        s += 'x'
                elif next_char in 'uU':

                    _ndigits = 4 if next_char == 'u' else 8
                    idx += 2
                    hex_str = ''
                    while idx < len(l2) and l2[idx] in '0123456789abcdefABCDEF' and len(hex_str) < _ndigits:
                        hex_str += l2[idx]
                        idx += 1
                    if len(hex_str) == _ndigits:
                        try:
                            s += chr(int(hex_str, 16))
                        except (ValueError, OverflowError):
                            print(f" warning - invalid \\{next_char} escape in: {l2!r}", file=sys.stderr)
                            s += next_char
                    else:
                        print(f" warning - '\\{next_char}' escape requires {_ndigits} hex digits; "
                              f"treated as literal characters in: {l2!r}", file=sys.stderr)
                        s += next_char + hex_str
                else:
                    s += next_char
                    idx += 2
            elif l2[idx] == '"':
                return s
            else:
                s += l2[idx]
                idx += 1
        print(f" warning - unterminated string literal: {l2!r}", file=sys.stderr)
        return s


class Parser:
    """Low-level token readers shared across the pattern-file and
    assembly-source parsers: numbers, symbol/label names, {}-bracketed
    expressions, and (via ExpressionEvaluator) full arithmetic. State-aware
    (needs state.swordchars/lwordchars, which a pattern file's .labelc
    directive can customize), unlike StringUtils."""

    def __init__(self, state):
        self.state = state

    def get_intstr(self, s, idx):
        """Read a run of decimal digits."""
        fs = ''
        while idx < len(s) and s[idx] in DIGIT:
            fs += s[idx]
            idx += 1
        return fs, idx

    def get_floatstr(self, s, idx):
        """Read a float literal: -inf/inf/nan, or digits[.digits][e[+-]digits].
        Backtracks to just the mantissa if an 'e'/'E' isn't followed by any
        exponent digits, so "2e" parses as "2" rather than consuming a
        dangling exponent marker."""
        if s[idx:idx + 4] == '-inf':
            return '-inf', idx + 4
        elif s[idx:idx + 3] == 'inf':
            return 'inf', idx + 3
        elif s[idx:idx + 3] == 'nan':
            return 'nan', idx + 3
        else:
            fs = ''
            while idx < len(s) and s[idx] in "0123456789.":
                fs += s[idx]
                idx += 1
            if idx < len(s) and s[idx] in "eE":
                saved_idx = idx
                saved_fs  = fs
                fs += s[idx]
                idx += 1
                if idx < len(s) and s[idx] in "+-":
                    fs += s[idx]
                    idx += 1
                digits_start = idx
                while idx < len(s) and s[idx] in "0123456789":
                    fs += s[idx]
                    idx += 1
                if idx == digits_start:
                    fs  = saved_fs
                    idx = saved_idx
            return fs, idx

    def isfloatstr(self, s, idx):
        """Whether a float literal starts at idx, without consuming it."""
        sidx = idx
        v, idx = self.get_floatstr(s, idx)
        if idx == sidx:
            return False
        else:
            return True

    def get_curlb(self, s, idx):
        """Read a {...} bracketed expression body verbatim (no nested-brace
        handling: the first '}' closes it), used by directives like .EQU and
        by qad{}/dbl{}/flt{} float notation. Returns (found, body, new_idx);
        found is False (with idx unchanged past leading space) if s[idx]
        isn't '{' at all."""
        idx = StringUtils.skipspc(s, idx)
        f = False
        t = ''

        if idx < len(s) and s[idx] == '{':
            idx += 1
            idx = StringUtils.skipspc(s, idx)
            while idx < len(s) and s[idx] != '}':
                t += s[idx]
                idx += 1
            if idx >= len(s):
                print(f" error - missing closing '}}' in expression: '{{{t}'", file=sys.stderr)
                return False, '', len(s)
            idx += 1
            f = True

        return f, t, idx

    def get_symbol_word(self, s, idx):
        """Read a .setsym-style symbol name (case-folded to upper), using
        state.swordchars as the valid character set so a pattern file's
        .labelc directive can widen/narrow what counts as a symbol
        character. May not start with a digit."""
        t = ""
        if idx < len(s) and s[idx] not in DIGIT and s[idx] in self.state.swordchars:
            t = s[idx]
            idx += 1
            while idx < len(s) and s[idx] in self.state.swordchars:
                t += s[idx]
                idx += 1
        return StringUtils.upper(t), idx

    def get_label_word(self, s, idx):
        """Read a label/directive name (case preserved, unlike symbols),
        using state.lwordchars, and additionally consume a trailing ':' that
        marks a label definition -- but not "::" (the .EQU-with-reloctype
        separator), so "label::abs64" isn't mistaken for a label-defining
        colon followed by ":abs64"."""
        t = ""
        if idx < len(s) and (s[idx] == '.' or (s[idx] not in DIGIT and s[idx] in self.state.lwordchars)):
            t = s[idx]
            idx += 1
            while idx < len(s) and s[idx] in self.state.lwordchars:
                t += s[idx]
                idx += 1

            if idx < len(s) and s[idx] == ':' and (idx + 1 >= len(s) or s[idx + 1] != '='):
                idx += 1

        return t, idx

    def get_params1(self, l, idx):
        """Read a pattern's operand-template text up to its "::" separator
        (the boundary before the encoding expression)."""
        idx = StringUtils.skipspc(l, idx)

        if idx >= len(l):
            return "", idx

        s = ""
        while idx < len(l):
            if l[idx:idx + 2] == '::':
                idx += 2
                break
            else:
                s += l[idx]
                idx += 1
        return s.rstrip(' \t'), idx


def enfloat(a):
    """Reinterpret a's low 32 bits as an IEEE-754 single-precision float
    (the inverse of packing a float into a 32-bit instruction field)."""
    try:
        float_value = struct.unpack('f', struct.pack('I', int(a) & 0xFFFFFFFF))[0]
    except (struct.error, OverflowError, ValueError):
        float_value = 0.0
    return float_value


def endouble(a):
    """Reinterpret a's low 64 bits as an IEEE-754 double."""
    try:
        double_value = struct.unpack('d', struct.pack('Q', int(a) & 0xFFFFFFFFFFFFFFFF))[0]
    except (struct.error, OverflowError, ValueError):
        double_value = 0.0
    return double_value


enflt = enfloat
endbl = endouble


class IEEE754Converter:
    """Converts a decimal string (or 'inf'/'-inf'/'nan') to its IEEE-754 bit
    pattern, as a hex string, for the 32-/64-/128-bit formats. The 32- and
    64-bit cases can lean on Python's own `struct`/float (which are IEEE-754
    under the hood); 128-bit ("binary128"/quad precision) has no native
    Python or struct support, so _decimal_to_ieee754_128bit_hex_impl()
    below builds the sign/exponent/fraction fields by hand using Decimal for
    the needed precision."""

    @staticmethod
    def decimal_to_ieee754_32bit_hex(a):
        if a == 'inf':
            return "0x7F800000"
        elif a == '-inf':
            return "0xFF800000"
        elif a == 'nan':
            return "0x7FC00000"

        try:
            fval = float(Decimal(a))
        except Exception as _e:
            raise ValueError(f"decimal_to_ieee754_32bit_hex: invalid input {a!r}") from _e
        try:
            bits = struct.unpack('I', struct.pack('f', fval))[0]
        except (struct.error, OverflowError) as _e:
            raise ValueError(f"decimal_to_ieee754_32bit_hex: cannot pack {fval!r}") from _e
        return f"0x{bits:08X}"

    @staticmethod
    def decimal_to_ieee754_64bit_hex(a):
        if a == 'inf':
            return "0x7FF0000000000000"
        elif a == '-inf':
            return "0xFFF0000000000000"
        elif a == 'nan':
            return "0x7FF8000000000000"

        try:
            fval = float(Decimal(a))
        except Exception as _e:
            raise ValueError(f"decimal_to_ieee754_64bit_hex: invalid input {a!r}") from _e
        try:
            bits = struct.unpack('Q', struct.pack('d', fval))[0]
        except (struct.error, OverflowError) as _e:
            raise ValueError(f"decimal_to_ieee754_64bit_hex: cannot pack {fval!r}") from _e
        return f"0x{bits:016X}"

    @staticmethod
    def decimal_to_ieee754_128bit_hex(a):
        with localcontext() as _ctx:
            _ctx.prec = 60
            return IEEE754Converter._decimal_to_ieee754_128bit_hex_impl(a)

    @staticmethod
    def _decimal_to_ieee754_128bit_hex_impl(a):
        """Build a binary128 bit pattern by hand: find the base-2 exponent
        via bit_length() on a fixed-point-scaled integer (avoiding float's
        53-bit mantissa, which can't represent this range/precision),
        normalize the mantissa into [1,2), then split into
        sign/exponent/fraction fields and round the fraction to
        SIGNIFICAND_BITS. Overflow rounds to +/-infinity; an unbiased
        exponent at or below 0 falls back to the subnormal encoding (fixed
        exponent field of 0, fraction scaled without the implicit leading
        1)."""
        BIAS = 16383
        SIGNIFICAND_BITS = 112
        EXPONENT_BITS = 15

        if a == 'inf':
            a = 'Infinity'
        elif a == '-inf':
            a = '-Infinity'
        elif a == 'nan':
            a = 'NaN'
        d = Decimal(a)

        if d.is_nan():
            sign = 0
            exponent = (1 << EXPONENT_BITS) - 1
            fraction = 1 << (SIGNIFICAND_BITS - 1)
        elif d == Decimal('Infinity'):
            sign = 0
            exponent = (1 << EXPONENT_BITS) - 1
            fraction = 0
        elif d == Decimal('-Infinity'):
            sign = 1
            exponent = (1 << EXPONENT_BITS) - 1
            fraction = 0
        elif d == 0:
            sign = 0
            exponent = 0
            fraction = 0
        else:
            sign = 0 if d >= 0 else 1
            d = abs(d)

            two = Decimal(2)

            scaled = int(d * (two ** SIGNIFICAND_BITS))
            if scaled == 0:
                exp_unbiased = -(BIAS - 1)
            else:
                exp_unbiased = scaled.bit_length() - 1 - SIGNIFICAND_BITS

            scale = two ** exp_unbiased
            normalized = d / scale

            while normalized >= 2:
                exp_unbiased += 1
                normalized /= 2
            while normalized < 1:
                exp_unbiased -= 1
                normalized *= 2

            biased_exp = exp_unbiased + BIAS

            _MAX_EXP = (1 << EXPONENT_BITS) - 1
            if biased_exp >= _MAX_EXP:
                sign_bit = sign
                exponent = _MAX_EXP
                fraction = 0
                bits = (sign_bit << 127) | (exponent << SIGNIFICAND_BITS) | fraction
                return f"0x{bits:032X}"

            if biased_exp <= 0:
                exponent = 0
                shift = two ** (1 - BIAS - SIGNIFICAND_BITS)
                fraction = int(d / shift + Decimal('0.5'))
                if fraction >= (1 << SIGNIFICAND_BITS):
                    # Rounded up past the largest subnormal into the
                    # smallest normal value (2**(1-BIAS)).
                    exponent = 1
                    fraction = 0
            else:
                exponent = biased_exp
                fraction = int((normalized - 1) * (two ** SIGNIFICAND_BITS) + Decimal('0.5'))
                if fraction >= (1 << SIGNIFICAND_BITS):
                    # Mantissa rounded up to 2**SIGNIFICAND_BITS (e.g. a
                    # value a hair below a power of two): carry into the
                    # exponent instead of silently wrapping the fraction
                    # back to 0 while leaving the exponent one power of
                    # two too low. If this pushes the exponent to
                    # _MAX_EXP, exponent=_MAX_EXP/fraction=0 is exactly
                    # the correct infinity encoding.
                    fraction = 0
                    exponent += 1

            fraction &= (1 << SIGNIFICAND_BITS) - 1

        bits = (sign << 127) | (exponent << SIGNIFICAND_BITS) | fraction
        return f"0x{bits:032X}"

    @staticmethod
    def decimal_eval_expr(text):
        """Evaluate a +,-,*,/ decimal arithmetic expression at 60 digits of
        precision (used for float literals like "3.14*2+1"), so results
        stay exact enough for the 128-bit conversion above rather than
        picking up float rounding error."""
        with localcontext() as _ctx:
            _ctx.prec = 60
            return IEEE754Converter._decimal_eval_expr_impl(text)

    @staticmethod
    def _decimal_eval_expr_impl(text):
        text = text.strip()

        def skip(s, i):
            while i < len(s) and s[i] in ' \t':
                i += 1
            return i

        def parse_number(s, i):
            i = skip(s, i)
            neg = False
            if i < len(s) and s[i] == '-':
                neg = True
                i += 1
                i = skip(s, i)
            for kw, dval in (('inf', Decimal('Infinity')), ('nan', Decimal('NaN'))):
                if s[i:i + len(kw)] == kw:
                    v = -dval if neg else dval
                    return v, i + len(kw)
            if i >= len(s) or s[i] not in '0123456789.':
                raise ValueError(f"expected number at {i!r}")
            start = i
            while i < len(s) and s[i] in '0123456789.':
                i += 1
            if i < len(s) and s[i] in 'eE':
                i += 1
                if i < len(s) and s[i] in '+-':
                    i += 1
                while i < len(s) and s[i] in '0123456789':
                    i += 1
            try:
                v = Decimal(s[start:i])
            except Exception as _e:
                raise ValueError(f"invalid decimal literal: {s[start:i]!r}") from _e
            return (-v if neg else v), i

        def parse_factor(s, i):
            i = skip(s, i)
            if i < len(s) and s[i] == '(':
                try:
                    v, i = parse_expr(s, i + 1)
                except RecursionError:
                    raise ValueError("decimal_eval_expr: expression nesting too deep")
                i = skip(s, i)
                if i < len(s) and s[i] == ')':
                    i += 1
                return v, i
            if i < len(s) and s[i] == '-':
                try:
                    v, i = parse_factor(s, i + 1)
                except RecursionError:
                    raise ValueError("decimal_eval_expr: expression nesting too deep")
                return -v, i
            if i < len(s) and s[i] == '+':
                try:
                    return parse_factor(s, i + 1)
                except RecursionError:
                    raise ValueError("decimal_eval_expr: expression nesting too deep")
            return parse_number(s, i)

        def parse_term(s, i):
            v, i = parse_factor(s, i)
            while True:
                i = skip(s, i)
                if i < len(s) and s[i] == '*':
                    t, i = parse_factor(s, i + 1)
                    v *= t
                elif i + 1 < len(s) and s[i] == '/' and s[i + 1] == '/':
                    t, i = parse_factor(s, i + 2)
                    if t == 0:
                        raise ZeroDivisionError("floor division by zero in qad{}")
                    v = Decimal(int(v // t))
                elif i < len(s) and s[i] == '/' and (i + 1 >= len(s) or s[i + 1] != '/'):
                    t, i = parse_factor(s, i + 1)
                    if t == 0:
                        raise ZeroDivisionError("division by zero in qad{}")
                    v /= t
                elif i < len(s) and s[i] == '%':
                    t, i = parse_factor(s, i + 1)
                    if t == 0:
                        raise ZeroDivisionError("modulo by zero in qad{}")
                    v = Decimal(int(v) % int(t))
                else:
                    break
            return v, i

        def parse_expr(s, i):
            v, i = parse_term(s, i)
            while True:
                i = skip(s, i)
                if i < len(s) and s[i] == '+':
                    t, i = parse_term(s, i + 1)
                    v += t
                elif i < len(s) and s[i] == '-':
                    t, i = parse_term(s, i + 1)
                    v -= t
                else:
                    break
            return v, i

        val, _ = parse_expr(text, 0)
        return IEEE754Converter.decimal_to_ieee754_128bit_hex(str(val))


class VariableManager:
    """Storage for the pattern file's single-letter capture variables
    (!a-!z, read back as A-Z in an encoding expression)."""

    def __init__(self, state):
        self.state = state

    def get(self, s):
        c = ord(StringUtils.upper(s))
        return self.state.vars[c - ord('A')]

    def put(self, s, v):
        """Store a captured value, normalizing its Python type: an integral
        Decimal/float becomes a plain int (so later bitwise/shift operators
        on it work), a genuinely fractional value stays float, and anything
        that can't be coerced to int (e.g. already-UNDEF-derived) is stored
        as-is rather than raising."""
        if StringUtils.upper(s) in CAPITAL:
            c = ord(StringUtils.upper(s))
            if isinstance(v, Decimal):
                if not v.is_finite():
                    self.state.vars[c - ord('A')] = float(v)
                elif v == v.to_integral_value():
                    self.state.vars[c - ord('A')] = int(v)
                else:
                    self.state.vars[c - ord('A')] = float(v)
            elif isinstance(v, float) and not v.is_integer():
                self.state.vars[c - ord('A')] = v
            else:
                try:
                    self.state.vars[c - ord('A')] = int(v)
                except (OverflowError, ValueError):
                    self.state.vars[c - ord('A')] = v


class LabelManager:
    """Owns state.labels: name -> [value, section, is_equ, is_imported,
    reloc_type?]. Label names are case-sensitive (unlike SymbolManager's
    .setsym symbols)."""

    def __init__(self, state):
        self.state = state

    def _section_relative_offset(self, name, word_pc):
        """Translate a raw, whole-assembly program counter (word_pc) into
        its position relative to the start of section `name` in the final
        output file, or None if word_pc doesn't fall in any recorded visit
        to that section.

        This exists because a label's stored value is always the raw pc at
        the moment it was defined, but a section that is entered more than
        once (.text -> .data -> .text) has its fragments concatenated
        contiguously in the actual output -- with any other section's bytes
        in between simply absent from `name`'s own byte stream. Two labels
        in the *same* section can therefore have a raw-pc difference that
        doesn't match their true final byte distance whenever another
        section was visited between them; converting both sides to this
        section-relative offset first fixes that (see get_value() below).

        First checks the already-closed fragments recorded in
        state.section_ranges (one entry per completed visit, in order), then
        falls back to state.sections[name]'s *current, still-open* visit
        (entry_pc = pc at the most recent re-entry, not yet appended to
        section_ranges since the section hasn't been left or closed yet).
        """
        ranges = [(rs, rl) for (rn, rs, rl) in self.state.section_ranges if rn == name]
        cum = 0
        for rs, rl in ranges:
            if rs <= word_pc <= rs + rl:
                return cum + (word_pc - rs)
            cum += rl
        entry = self.state.sections.get(name)
        if entry:
            entry_pc = entry[2] if len(entry) > 2 else entry[0]
            if word_pc >= entry_pc:
                return cum + (word_pc - entry_pc)
        return None

    def get_section(self, k):
        # Same fix as get_value() above: only ever set the flag, never
        # clear it on success, so it doesn't clobber a sibling lookup's
        # earlier failure within the same expression.
        try:
            v = self.state.labels[k][1]
        except (KeyError, IndexError):
            v = UNDEF
            self.state.error_undefined_label = True
        return v

    def get_value(self, k):
        """Look up label k's value, converting it to a section-relative
        offset (see _section_relative_offset() above) in the two specific
        situations where that's actually safe and needed:

        - Inside a reloc_type-less .EQU's expression (state._equ_sections_touched
          is the set of every section touched so far by this .EQU; also used
          afterward to warn if it spans more than one section). A .EQU
          without an explicit reloc type bakes its result in as a fixed
          constant with no linker fixup, so it must already be correct for
          the *output* layout, not the assembler's internal pc numbering.
        - While actually encoding an instruction's object-code bytes
          (state._in_binary_list), and only when the referenced label lives
          in the *same* section currently being written to. $$/$. (the
          current-instruction pc markers) are converted the same way, so a
          pattern's "label - $$" arithmetic stays internally consistent.
          A cross-section reference is deliberately left as a raw value:
          the existing ELF relocation machinery already resolves those
          correctly, and converting only one side of a cross-section
          subtraction would make things worse, not better.

        Any other caller (e.g. a plain .EQU without reloc_type touching an
        *unrelated* section, or generic expression evaluation outside both
        of the above) gets the raw stored value untouched.
        """
        # Bugfix: this used to unconditionally reset error_undefined_label
        # to False here, on every single lookup. That clobbers the signal
        # from an EARLIER label reference in the same compound expression
        # (e.g. "undefined_label + defined_label": the first operand's
        # lookup correctly sets the flag, but the second operand's lookup
        # -- succeeding -- reset it right back to False, since none of the
        # binary-operator levels (term0..term11) save/restore or OR-merge
        # the flag around each operand). The net effect: only the LAST
        # label reference evaluated in an expression determined whether
        # ".ORG"/".RESB"/".ZERO"/the main instruction-encoding check ever
        # saw an undefined-label error at all -- an expression referencing
        # one undefined and one defined label could silently encode as if
        # correct, with no error printed. Only ever SET the flag (on
        # failure) here; never clear it on success, so it correctly
        # accumulates for the whole expression. Top-level callers that
        # need a "fresh" check (.ORG/.RESB/.ZERO/etc.) reset it themselves
        # immediately before evaluating their own expression.
        try:
            v = self.state.labels[k][0]
        except (KeyError, IndexError):
            if self.state.pas == 1 and k in self.state._relax_prev_values:
                return self.state._relax_prev_values[k]
            if self.state._pass1_size_mode:
                return 0
            v = UNDEF
            self.state.error_undefined_label = True
            if not self.state._in_match_attempt and (self.state.should_report_errors()):
                _fn = self.state.current_file or ""
                _ln = self.state.ln
                print(f" error - Label undefined: '{k}'"
                      f"  [{_fn}:{_ln}]", file=sys.stderr)
            return v
        _sec = self.state.labels[k][1]
        if self.state._equ_sections_touched is not None:
            self.state._equ_sections_touched.add(_sec)

            _adj = self._section_relative_offset(_sec, v)
            if _adj is not None:
                v = _adj
        elif self.state._in_binary_list and _sec == self.state.current_section:

            _adj = self._section_relative_offset(_sec, v)
            if _adj is not None:
                v = _adj

        # ELF relocation tracking: a plain .equ constant needs no relocation
        # (it's a fixed value baked in directly), so only track address
        # labels, or a .equ that explicitly asked for one via ::reloctype.
        _is_equ = len(self.state.labels[k]) > 2 and self.state.labels[k][2]
        _equ_has_reloc = _is_equ and len(self.state.labels[k]) > 4 and self.state.labels[k][4] is not None
        if self.state._elf_tracking and not self.state.error_undefined_label and (not _is_equ or _equ_has_reloc):
            if self.state._elf_capturing_var is not None:
                # PatternMatcher is capturing a !x-style variable: remember
                # which label it came from. A second write to the same
                # variable means the expression combined more than one label
                # (e.g. "label1+label2"), which can't map to a single
                # relocation, so mark it as such (None) instead.
                cv = self.state._elf_capturing_var
                if cv not in self.state._elf_var_to_label:
                    self.state._elf_var_to_label[cv] = (k, v)
                else:
                    self.state._elf_var_to_label[cv] = None
            elif self.state._elf_current_word_idx >= 0:
                # Inside makeobj(): a direct label reference in the object-code
                # expression itself (not via a captured pattern variable).
                self.state._elf_label_refs_seen.append(
                    (k, v, self.state._elf_current_word_idx))
        return v

    def put_value(self, k, v, s, is_equ=False, reloc_type=None):
        """Define/redefine label k. On Pass 1, redefining an existing label
        is an error unless the existing entry was only an imported
        placeholder (which a real local definition is allowed to replace).
        On Pass 2, every label must already exist from Pass 1 -- a
        first-time definition there would mean the two passes saw different
        source, which should never happen."""
        if self.state.pas == 1 or self.state.pas == 0:
            if k in self.state.labels:
                existing = self.state.labels[k]
                old_is_imported = len(existing) > 3 and existing[3]
                if not old_is_imported:
                    self.state.error_label_conflict = True
                    self.state.had_error = True
                    print(" error - label already defined.", file=sys.stderr)
                    return False
        elif self.state.pas == 2:
            if k not in self.state.labels:
                self.state.error_label_conflict = True
                self.state.had_error = True
                print(f" error - label '{k}' not defined in pass 1.", file=sys.stderr)
                return False

        if k in self.state.patsymbols:
            self.state.had_error = True
            print(f" error - '{k}' is a pattern file symbol.", file=sys.stderr)
            return False

        self.state.error_label_conflict = False

        is_imported = False

        entry = [v, s, is_equ, is_imported]
        if reloc_type is not None:
            entry.append(reloc_type)

        self.state.labels[k] = entry
        return True

    def printlabels(self):
        """Dump every label's value/section to stderr (used by the
        interactive "?" command)."""
        result = {}
        for key, value in self.state.labels.items():
            num = value[0]
            section = value[1]
            if num == UNDEF:
                num_str = "UNDEF"
            elif isinstance(num, float):
                num_str = repr(num)
            else:
                try:
                    num_str = hex(int(num))
                except (TypeError, ValueError, OverflowError):
                    num_str = repr(num)
            result[key] = [num_str, section]
        for k, v in sorted(result.items()):
            print(f"  {k:40s}  {v[0]}  ({v[1]})", file=sys.stderr)


class SymbolManager:
    """Owns state.symbols: the pattern file's .setsym-defined symbols
    (register names, etc.), looked up case-insensitively (unlike labels)."""

    def __init__(self, state):
        self.state = state

    def get(self, w):
        w = w.upper()
        return self.state.symbols.get(w, "")


class ExpressionEvaluator:
    """Recursive-descent arithmetic expression parser/evaluator, used for
    both pattern-file encoding expressions and assembly-source address
    expressions. The chain runs low-to-high precedence: expression() ->
    term11() -> term10() -> ... -> term0() -> term0_0() -> factor() ->
    factor1(), where each termN handles exactly one precedence level and
    factor()/factor1() bottom out at the smallest units that can't be split
    further (numeric/string/char literals, $$/$./#symbol, qad{}/dbl{}/flt{}
    float notation, label/variable references)."""

    def __init__(self, state, var_manager, label_manager, symbol_manager, parser):
        self.state = state
        self.var_manager = var_manager
        self.label_manager = label_manager
        self.symbol_manager = symbol_manager
        self.parser = parser

    def nbit(self, l):
        """Number of bits needed to represent abs(l) (the '@' unary operator
        below); NaN/inf have no meaningful bit width, so both return 0."""
        b = 0
        if isinstance(l, float) and not l == l:
            return 0
        if isinstance(l, float) and (l == float('inf') or l == float('-inf')):
            return 0
        try:
            r = int(abs(l))
        except (OverflowError, ValueError):
            return 0
        while r:
            r >>= 1
            b += 1
        return b

    def err(self, m):
        print(m, file=sys.stderr)
        return -1

    def factor(self, s, idx):
        """Bottom of the precedence chain: literals, unary operators
        (-,~,@), the *(value,byteoffset) byte-extract form, and (via
        factor1()) everything else that can't be decomposed further."""
        idx = StringUtils.skipspc(s, idx)
        x = 0

        if idx + 4 <= len(s) and s[idx:idx + 4] == '!!!!' and self.state.expmode == EXP_PAT:
            # End-of-VLIW-packet marker, valid only inside a pattern's own
            # encoding expression (EXP_PAT): whether this packet was closed
            # with "!!!!" (state.vliwstop, set by VLIWProcessor).
            x = self.state.vliwstop
            idx += 4
        elif idx + 3 <= len(s) and s[idx:idx + 3] == '!!!' and self.state.expmode == EXP_PAT:
            # "!!!" evaluates to the current VLIW slot count (state.vcnt),
            # also pattern-file-only.
            x = self.state.vcnt
            idx += 3
        elif idx < len(s) and s[idx] == '-':
            try:
                x, idx = self.factor(s, idx + 1)
            except RecursionError:
                if self.state.should_report_errors():
                    print(" error - expression nesting too deep (RecursionError) in unary '-'.", file=sys.stderr)
                return 0, idx
            x = -x
        elif idx < len(s) and s[idx] == '~':
            try:
                x, idx = self.factor(s, idx + 1)
            except RecursionError:
                if self.state.should_report_errors():
                    print(" error - expression nesting too deep (RecursionError) in unary '~'.", file=sys.stderr)
                return 0, idx
            try:
                x = ~int(x)
            except (OverflowError, ValueError):
                if self.state.should_report_errors():
                    print(" error - cannot apply bitwise NOT (~) to non-finite float value.", file=sys.stderr)
                x = 0
        elif idx < len(s) and s[idx] == '@':
            try:
                x, idx = self.factor(s, idx + 1)
            except RecursionError:
                if self.state.should_report_errors():
                    print(" error - expression nesting too deep (RecursionError) in unary '@'.", file=sys.stderr)
                return 0, idx
            x = self.nbit(x)
        elif idx < len(s) and s[idx] == '*':
            # *(value, byte_index) extracts byte number `byte_index`
            # (0=least-significant) from `value`, used by patterns that need
            # to split a multi-byte computed value across several encoded
            # bytes.
            if idx + 1 < len(s) and s[idx + 1] == '(':
                x, idx = self.expression(s, idx + 2)
                if idx < len(s) and s[idx] == ',':
                    x2, idx = self.expression(s, idx + 1)
                    if idx < len(s) and s[idx] == ')':
                        idx += 1
                        try:
                            shift_amount = int(x2) * 8
                        except (OverflowError, ValueError):
                            if self.state.should_report_errors():
                                print(" error - non-finite byte-extract offset in *(expr, expr).", file=sys.stderr)
                            x = 0
                        else:
                            if shift_amount < 0:
                                if self.state.should_report_errors():
                                    print(" error - negative byte-extract offset in *(expr, expr).", file=sys.stderr)
                                x = 0
                            else:
                                x = x >> shift_amount
                    else:
                        print(" error - missing ')' in *(expr, expr) expression.", file=sys.stderr)
                        x = 0
                else:
                    print(" error - missing ',' in *(expr, expr) expression.", file=sys.stderr)
                    x = 0
            else:
                print(" error - expected '(' after '*' in *(expr,expr) expression.", file=sys.stderr)
        else:
            prev_idx = idx
            x, idx = self.factor1(s, idx)
            if (idx == prev_idx
                    and idx < len(s)
                    and s[idx] not in (chr(0), ',', ')', ']', CB, ' ', '\t')
                    and not self.state._in_match_attempt
                    and (self.state.should_report_errors())):
                print(f" warning - unrecognized token at position {idx} in expression: "
                      f"{s[idx:idx + 8]!r} (treated as 0)", file=sys.stderr)
        idx = StringUtils.skipspc(s, idx)
        return x, idx

    def xeval(self, x, _=None):
        """Evaluate the body of a qad{}/dbl{}/flt{} float-notation expression
        (a string that may reference labels via ":name" and call
        enfloat/endouble/enflt/endbl), *without* using Python's own eval()
        on untrusted input directly. Label references are first substituted
        with unique numeric placeholders (so a label named e.g. "e" can't be
        confused with Python's exponent syntax), then the result is parsed
        with ast.parse() and walked by hand (_ev() below), allowing only a
        small fixed set of literal/operator/call node types -- arbitrary
        code execution is never reachable even though the input text
        ultimately comes from the assembly source or pattern file."""
        def _cc_escape(chars):
            out = []
            for c in chars:
                if c == '\\':
                    out.append('\\\\')
                elif c == ']':
                    out.append('\\]')
                elif c == '^':
                    out.append('\\^')
                elif c == '-':
                    out.append('\\-')
                else:
                    out.append(re.escape(c))
            return ''.join(out)

        escaped = _cc_escape(self.state.lwordchars)
        pattern = rf":([{escaped}]+)(?=[^{escaped}]|$)"

        _tag = "_AXXLBL_" + uuid.uuid4().hex
        _label_values = {}

        def replacer(match):
            label_name = match.group(1)
            placeholder = f"{_tag}{len(_label_values)}"
            try:
                val = self.state.labels[label_name][0]
            except (KeyError, IndexError):
                self.state.error_undefined_label = True
                _label_values[placeholder] = 0
                return placeholder
            if _is_undef_derived(val):
                self.state.error_undefined_label = True
                _label_values[placeholder] = 0
                return placeholder
            _is_equ = (len(self.state.labels.get(label_name, [])) > 2
                       and self.state.labels[label_name][2])
            if self.state._elf_tracking and not _is_equ:
                if self.state._elf_capturing_var is not None:
                    cv = self.state._elf_capturing_var
                    if cv not in self.state._elf_var_to_label:
                        self.state._elf_var_to_label[cv] = (label_name, val)
                    else:
                        self.state._elf_var_to_label[cv] = None
                elif self.state._elf_current_word_idx >= 0:
                    self.state._elf_label_refs_seen.append(
                        (label_name, val, self.state._elf_current_word_idx))
            try:
                _label_values[placeholder] = int(val)
            except (TypeError, ValueError, OverflowError):
                self.state.error_undefined_label = True
                _label_values[placeholder] = 0
            return placeholder

        s = re.sub(pattern, replacer, x)

        _ALLOWED_FUNCS = {
            "enfloat": enfloat, "endouble": endouble,
            "enflt": enflt, "endbl": endbl,
        }

        try:
            tree = ast.parse(s, mode='eval')
        except SyntaxError as e:
            raise ValueError(f"xeval: parse error in '{s}': {e}")

        def _ev(node):
            if isinstance(node, ast.Expression):
                return _ev(node.body)
            if isinstance(node, ast.Constant):
                if isinstance(node.value, (int, float, bool)):
                    return node.value
                raise ValueError(f"xeval: disallowed constant {node.value!r} in '{s}'")
            if isinstance(node, ast.BinOp):
                l = _ev(node.left)
                r = _ev(node.right)
                op = node.op
                if isinstance(op, ast.Add):
                    return l + r
                if isinstance(op, ast.Sub):
                    return l - r
                if isinstance(op, ast.Mult):
                    return l * r
                if isinstance(op, ast.Div):
                    return l / r
                if isinstance(op, ast.FloorDiv):
                    return l // r
                if isinstance(op, ast.Mod):
                    return l % r
                if isinstance(op, ast.Pow):
                    if isinstance(r, int) and r > 1024:
                        raise ValueError("xeval: exponent exceeds 1024")
                    return l ** r
                if isinstance(op, ast.BitAnd):
                    return l & r
                if isinstance(op, ast.BitOr):
                    return l | r
                if isinstance(op, ast.BitXor):
                    return l ^ r
                if isinstance(op, ast.LShift):
                    if isinstance(r, int) and r > 65536:
                        raise ValueError("xeval: shift count exceeds 65536")
                    return l << r
                if isinstance(op, ast.RShift):
                    return l >> r
                raise ValueError(f"xeval: disallowed operator {type(op).__name__} in '{s}'")
            if isinstance(node, ast.UnaryOp):
                v = _ev(node.operand)
                op = node.op
                if isinstance(op, ast.UAdd):
                    return +v
                if isinstance(op, ast.USub):
                    return -v
                if isinstance(op, ast.Invert):
                    return ~v
                raise ValueError(f"xeval: disallowed unary operator {type(op).__name__} in '{s}'")
            if isinstance(node, ast.BoolOp):
                if isinstance(node.op, ast.And):
                    res = True
                    for vn in node.values:
                        res = _ev(vn)
                        if not res:
                            return res
                    return res
                if isinstance(node.op, ast.Or):
                    res = False
                    for vn in node.values:
                        res = _ev(vn)
                        if res:
                            return res
                    return res
                raise ValueError(f"xeval: disallowed bool operator in '{s}'")
            if isinstance(node, ast.Compare):
                left = _ev(node.left)
                for cop, comp in zip(node.ops, node.comparators):
                    right = _ev(comp)
                    if   isinstance(cop, ast.Eq):
                        ok = left == right
                    elif isinstance(cop, ast.NotEq):
                        ok = left != right
                    elif isinstance(cop, ast.Lt):
                        ok = left <  right
                    elif isinstance(cop, ast.LtE):
                        ok = left <= right
                    elif isinstance(cop, ast.Gt):
                        ok = left >  right
                    elif isinstance(cop, ast.GtE):
                        ok = left >= right
                    else:
                        raise ValueError(f"xeval: disallowed comparison in '{s}'")
                    if not ok:
                        return False
                    left = right
                return True
            if isinstance(node, ast.IfExp):
                return _ev(node.body) if _ev(node.test) else _ev(node.orelse)
            if isinstance(node, ast.Call):
                if (not isinstance(node.func, ast.Name)
                        or node.func.id not in _ALLOWED_FUNCS):
                    raise ValueError(f"xeval: disallowed function call in '{s}'")
                if node.keywords:
                    raise ValueError(f"xeval: keyword arguments not allowed in '{s}'")
                args = [_ev(a) for a in node.args]
                return _ALLOWED_FUNCS[node.func.id](*args)
            if isinstance(node, ast.Name):
                if node.id in _label_values:
                    return _label_values[node.id]
                raise ValueError(f"xeval: disallowed name '{node.id}' in '{s}'")
            raise ValueError(
                f"xeval: disallowed AST node {type(node).__name__} in '{s}'")

        result = _ev(tree)
        if not isinstance(result, (int, float, bool)):
            raise ValueError(f"xeval: unsafe result type {type(result)}")
        return result

    def factor1(self, s, idx):
        """The rest of factor()'s job: parenthesized sub-expressions, C-style
        character-literal escapes ('\\t', '\\'', 'a', ...), $$/$./#symbol,
        qad{}/dbl{}/flt{} float notation (via xeval() above), numeric
        literals in the pattern file's default hex radix, and finally
        label/pattern-variable name references."""
        x = 0
        idx = StringUtils.skipspc(s, idx)

        if idx >= len(s):
            return x, idx

        if s[idx] == '(':
            x, idx = self.expression(s, idx + 1)
            if idx < len(s) and s[idx] == ')':
                idx += 1
            else:
                print(" error - missing closing ')' in expression.", file=sys.stderr)
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\t'":
            x = 0x09
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\''":
            x = ord("'")
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\\\'":
            x = ord("\\")
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\n'":
            x = 0x0a
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\0'":
            x = 0x00
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\r'":
            x = 0x0d
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\a'":
            x = 0x07
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\b'":
            x = 0x08
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\f'":
            x = 0x0c
            idx += 4
        elif idx + 4 <= len(s) and s[idx:idx + 4] == "'\\v'":
            x = 0x0b
            idx += 4
        elif (_hexlit := StringUtils.parse_hex_char_literal(s, idx))[0]:
            x, idx = _hexlit[1], _hexlit[2]
        elif idx + 3 <= len(s) and s[idx] == '\'' and s[idx + 1] != '\\' and s[idx + 2] == '\'':
            x = ord(s[idx + 1])
            idx += 3
        elif StringUtils.q(s, '$$', idx):
            idx += 2
            _raw = self.state.pc_instr_start if self.state._in_binary_list else self.state.pc

            if self.state._in_binary_list or self.state._equ_sections_touched is not None:
                _adj = self.label_manager._section_relative_offset(self.state.current_section, _raw)
                x = _adj if _adj is not None else _raw
            else:
                x = _raw
        elif StringUtils.q(s, '$.', idx):
            idx += 2
            _raw = self.state.pc_instr_end
            if self.state._in_binary_list or self.state._equ_sections_touched is not None:
                _adj = self.label_manager._section_relative_offset(self.state.current_section, _raw)
                x = _adj if _adj is not None else _raw
            else:
                x = _raw
        elif StringUtils.q(s, '#', idx):
            idx += 1
            t, idx = self.parser.get_symbol_word(s, idx)
            _sym_val = self.symbol_manager.get(t)
            if _sym_val == "":
                if self.state.should_report_errors():
                    print(f" error - undefined symbol: '#{t}'", file=sys.stderr)
                x = 0
            else:
                x = _sym_val
        elif StringUtils.q(s, '0b', idx):
            idx += 2
            while idx < len(s) and s[idx] in "01":
                x = 2 * x + int(s[idx], 2)
                idx += 1
        elif StringUtils.q(s, '0x', idx):
            idx += 2
            while idx < len(s) and StringUtils.upper(s[idx]) in XDIGIT:
                x = 16 * x + int(s[idx].lower(), 16)
                idx += 1
        elif (idx + 3 <= len(s) and s[idx:idx + 3] == 'qad'
              and (lambda _j=StringUtils.skipspc(s, idx + 3): _j < len(s) and s[_j] == '{')()):
            idx += 3
            idx = StringUtils.skipspc(s, idx)
            if idx < len(s) and s[idx] == '{':
                f, t, idx = self.parser.get_curlb(s, idx)
                if not f:
                    pass
                else:
                    try:
                        h = IEEE754Converter.decimal_eval_expr(t)
                    except (ValueError, ZeroDivisionError):
                        try:
                            v = self.xeval(t, None)
                        except (ValueError, TypeError, OverflowError, ZeroDivisionError):

                            if self.state.should_report_errors():
                                print(f" error - qad{{}}: cannot evaluate expression '{t}'; using 0.", file=sys.stderr)
                            h = '0' * 32
                        else:
                            if isinstance(v, int) or (
                                    isinstance(v, float) and v.is_integer()):
                                h = IEEE754Converter.decimal_to_ieee754_128bit_hex(
                                        str(int(v)))
                            else:
                                h = IEEE754Converter.decimal_to_ieee754_128bit_hex(
                                        str(Decimal(repr(float(v)))))
                    x = int(h, 16)
        elif (idx + 3 <= len(s) and s[idx:idx + 3] == 'dbl'
              and (lambda _j=StringUtils.skipspc(s, idx + 3): _j < len(s) and s[_j] == '{')()):
            idx += 3
            f, t, idx = self.parser.get_curlb(s, idx)
            if f:
                if t == 'nan':
                    x = 0x7ff8000000000000
                elif t == 'inf':
                    x = 0x7ff0000000000000
                elif t == '-inf':
                    x = 0xfff0000000000000
                else:
                    try:
                        v = float(self.xeval(t, None))
                        x = int.from_bytes(struct.pack('>d', v), "big")
                    except (OverflowError, ValueError, TypeError, struct.error, ZeroDivisionError):
                        if self.state.should_report_errors():
                            print(" error - dbl{}: cannot convert expression to float64; using 0.", file=sys.stderr)
                        x = 0
        elif (idx + 3 <= len(s) and s[idx:idx + 3] == 'flt'
              and (lambda _j=StringUtils.skipspc(s, idx + 3): _j < len(s) and s[_j] == '{')()):
            idx += 3
            f, t, idx = self.parser.get_curlb(s, idx)
            if f:
                if t == 'nan':
                    x = 0x7fc00000
                elif t == 'inf':
                    x = 0x7f800000
                elif t == '-inf':
                    x = 0xff800000
                else:
                    try:
                        v = float(self.xeval(t, None))
                        x = int.from_bytes(struct.pack('>f', v), "big")
                    except (OverflowError, ValueError, TypeError, struct.error, ZeroDivisionError):
                        if self.state.should_report_errors():
                            print(" error - flt{}: cannot convert expression to float32; using 0.", file=sys.stderr)
                        x = 0
        elif (idx + 5 <= len(s) and s[idx:idx + 5] == 'enflt'
              and (lambda _j=StringUtils.skipspc(s, idx + 5): _j < len(s) and s[_j] == '{')()):
            idx += 5
            f, t, idx = self.parser.get_curlb(s, idx)
            if f:
                _outer_undef = self.state.error_undefined_label
                self.state.error_undefined_label = False
                v, _ = self.expression(t + chr(0), 0)
                _inner_undef = self.state.error_undefined_label
                self.state.error_undefined_label = _outer_undef or _inner_undef
                if _inner_undef:
                    if self.state.should_report_errors():
                        print(" error - enflt{}: expression contains undefined label.", file=sys.stderr)
                    x = enflt(0)
                else:
                    try:
                        x = enflt(int(v) & 0xFFFFFFFF)
                    except (OverflowError, ValueError):
                        if self.state.should_report_errors():
                            print(" error - enflt{}: non-finite float value; using 0.", file=sys.stderr)
                        x = enflt(0)
        elif (idx + 5 <= len(s) and s[idx:idx + 5] == 'endbl'
              and (lambda _j=StringUtils.skipspc(s, idx + 5): _j < len(s) and s[_j] == '{')()):
            idx += 5
            f, t, idx = self.parser.get_curlb(s, idx)
            if f:
                _outer_undef = self.state.error_undefined_label
                self.state.error_undefined_label = False
                v, _ = self.expression(t + chr(0), 0)
                _inner_undef = self.state.error_undefined_label
                self.state.error_undefined_label = _outer_undef or _inner_undef
                if _inner_undef:
                    if self.state.should_report_errors():
                        print(" error - endbl{}: expression contains undefined label.", file=sys.stderr)
                    x = endbl(0)
                else:
                    try:
                        x = endbl(int(v) & 0xFFFFFFFFFFFFFFFF)
                    except (OverflowError, ValueError):
                        if self.state.should_report_errors():
                            print(" error - endbl{}: non-finite float value; using 0.", file=sys.stderr)
                        x = endbl(0)
        elif idx + 4 <= len(s) and s[idx:idx + 4] == 'not(':
            # not(expr): logical negation, written as a call-like form rather
            # than a prefix operator so it reads unambiguously in pattern
            # text. Handled here (factor1(), the base of the precedence
            # chain) rather than at some higher termN level, so that its
            # result is just an ordinary atom to every operator above it
            # (+, -, comparisons, &&, ||, ?:) on EITHER side -- e.g.
            # "not(0)+5" must mean "(not(0))+5", not "not(0+5)". Bugfix:
            # this used to live in term8 (between term7 comparisons and
            # term9 &&), which meant only operators ABOVE term8 (&&, ||,
            # ternary) got a chance to combine with its result via their own
            # while-loops; anything BELOW term8 (comparisons, +/-, etc.) is
            # only ever invoked while parsing a fresh left-hand operand, so
            # a trailing "+5" after "not(0)" was silently left unconsumed
            # by the level that used to handle it, and unnoticed here.
            x, idx = self.expression(s, idx + 4)
            idx = StringUtils.skipspc(s, idx)
            if idx < len(s) and s[idx] == ')':
                idx += 1
            else:
                print(" error - missing closing ')' in not(...) expression.", file=sys.stderr)
            x = 0 if x else 1
        elif self.state.exp_typ == 'i' and idx < len(s) and s[idx].isdigit():
                fs, idx = self.parser.get_intstr(s, idx)
                x = int(fs)
        elif self.state.exp_typ == 'f' and idx < len(s) and (self.parser.isfloatstr(s, idx)):
                fs, idx = self.parser.get_floatstr(s, idx)
                try:
                    x = float(fs) if fs else 0.0
                except ValueError:
                    x = 0.0
        elif (idx < len(s) and
              s[idx] in LOWER and (idx + 1 >= len(s) or s[idx + 1] not in self.state.lwordchars)):
            ch = s[idx]
            if idx + 3 <= len(s) and s[idx + 1:idx + 3] == ':=':
                x, idx = self.expression(s, idx + 3)
                self.var_manager.put(ch, x)
            else:
                x = self.var_manager.get(ch)
                idx += 1
                if (not self.state._in_match_attempt
                        and not self.state._pass1_size_mode
                        and (self.state.should_report_errors())
                        and _is_undef_derived(x)):
                    self.state.error_undefined_label = True
                    print(f" error - Label undefined: variable '{ch}' contains undefined value"
                          f"  [{self.state.current_file}:{self.state.ln}]", file=sys.stderr)
                if (self.state._elf_tracking
                        and self.state._elf_current_word_idx >= 0):
                    entry = self.state._elf_var_to_label.get(ch)
                    if entry is not None:
                        lname, lval = entry
                        self.state._elf_label_refs_seen.append(
                            (lname, lval, self.state._elf_current_word_idx))
        elif idx < len(s) and s[idx] in self.state.lwordchars:
            w, idx_new = self.parser.get_label_word(s, idx)
            if idx != idx_new:
                idx = idx_new
                x = self.label_manager.get_value(w)

        idx = StringUtils.skipspc(s, idx)
        return x, idx

    def term0_0(self, s, idx):
        """Highest-precedence binary operator: ** (exponentiation). Capped
        both on the exponent itself and on the estimated result bit-length,
        so a chained "2**2**2**..." or a huge exponent can't blow up into an
        unbounded/extremely slow big-integer computation."""
        x, idx = self.factor(s, idx)
        while idx < len(s) and StringUtils.q(s, '**', idx):
            t, idx = self.factor(s, idx + 2)
            _EXP_MAX = 1024
            _EXP_RESULT_MAX_BITS = 1 << 20

            try:
                t_int = int(t)
            except (ValueError, OverflowError):
                t_int = 0
            if t_int < 0:
                self.err("Negative exponent in ** expression; result set to 0.")
                x = 0
                break
            if t_int > _EXP_MAX:
                self.err(f"Exponent {t_int} exceeds maximum {_EXP_MAX} in ** expression; result set to 0.")
                x = 0
                break

            try:
                _base_bits = abs(x).bit_length() if isinstance(x, int) else 1024
            except (TypeError, ValueError, OverflowError):
                _base_bits = 1024
            if _base_bits * max(t_int, 1) > _EXP_RESULT_MAX_BITS:
                self.err(f"** result would exceed {_EXP_RESULT_MAX_BITS} bits "
                         f"(chained exponentiation); result set to 0.")
                x = 0
                break
            try:
                x = x ** t_int
            except OverflowError:
                self.err("** result is too large to represent as a float; result set to 0.")
                x = 0
                break
            if isinstance(x, float) and x.is_integer():
                x = int(x)
        return x, idx

    def term0(self, s, idx):
        """*, //, /, % (multiplication/division/modulo). Integer / falls
        back to float division only when the operands don't divide evenly,
        warning if that loses precision for very large operands; // and %
        guard against division by zero."""
        x, idx = self.term0_0(s, idx)
        while idx < len(s):
            if s[idx] == '*' and (idx + 1 >= len(s) or s[idx + 1] != '*'):
                t, idx = self.term0_0(s, idx + 1)
                x *= t
            elif StringUtils.q(s, '//', idx):
                t, idx = self.term0_0(s, idx + 2)
                if t == 0:
                    # Bugfix: self.err() here used to print a bare
                    # "Division by 0 error." with no " error -" prefix and
                    # no had_error, so a division-by-zero in an ordinary
                    # instruction operand silently produced a plausible-
                    # looking 0 with a build that still reported success.
                    if self.state.should_report_errors():
                        print(" error - Division by 0 error.", file=sys.stderr)
                        self.state.had_error = True
                    x = 0
                    break
                else:
                    x //= t
            elif s[idx] == '/':
                t, idx = self.term0_0(s, idx + 1)
                if t == 0:
                    if self.state.should_report_errors():
                        print(" error - Division by 0 error.", file=sys.stderr)
                        self.state.had_error = True
                    x = 0
                    break
                else:
                    if isinstance(x, int) and isinstance(t, int):
                        q, r = divmod(x, t)
                        if r == 0:
                            x = q
                        else:

                            if ((abs(x) >= (1 << 53) or abs(t) >= (1 << 53))
                                    and self.state.should_report_errors()):
                                print(f" warning - dividing large integers ({x} / {t}) that do "
                                      f"not divide evenly loses precision when converted to a "
                                      f"float; result may not be exact.", file=sys.stderr)
                            x = x / t
                    else:
                        x = x / t
            elif s[idx] == '%':
                t, idx = self.term0_0(s, idx + 1)
                if t == 0:
                    if self.state.should_report_errors():
                        print(" error - Division by 0 error.", file=sys.stderr)
                        self.state.had_error = True
                    x = 0
                    break
                else:
                    x = x % t
            else:
                break
        return x, idx

    def term1(self, s, idx):
        """+, - (addition/subtraction)."""
        x, idx = self.term0(s, idx)
        while idx < len(s):
            if s[idx] == '+':
                t, idx = self.term0(s, idx + 1)
                x += t
            elif s[idx] == '-':
                t, idx = self.term0(s, idx + 1)
                x -= t
            else:
                break
        return x, idx

    def term2(self, s, idx):
        """<<, >> (bit shift). Shift count is capped and rejected if
        negative, both to avoid a pathologically slow/huge big-integer
        shift from a malformed expression."""
        x, idx = self.term1(s, idx)
        _SHIFT_MAX = 65536
        while idx < len(s):
            if StringUtils.q(s, '<<', idx):
                t, idx = self.term1(s, idx + 2)
                try:
                    x = int(x)
                    t = int(t)
                except (ValueError, OverflowError):
                    x = 0
                    break
                if t < 0:
                    if self.state.should_report_errors():
                        print(f" error - negative shift count ({t}) in << expression.", file=sys.stderr)
                    x = 0
                    break
                if t > _SHIFT_MAX:
                    if self.state.should_report_errors():
                        print(f" error - shift count {t} exceeds maximum {_SHIFT_MAX} in << expression.", file=sys.stderr)
                    x = 0
                    break
                x <<= t
            elif StringUtils.q(s, '>>', idx):
                t, idx = self.term1(s, idx + 2)
                try:
                    x = int(x)
                    t = int(t)
                except (ValueError, OverflowError):
                    x = 0
                    break
                if t < 0:
                    if self.state.should_report_errors():
                        print(f" error - negative shift count ({t}) in >> expression.", file=sys.stderr)
                    x = 0
                    break
                if t > _SHIFT_MAX:
                    x = 0
                    break
                x >>= t
            else:
                break
        return x, idx

    def _safe_int(self, v, op_name):
        try:
            return int(v)
        except (OverflowError, ValueError):
            if self.state.should_report_errors():
                print(f" error - non-finite value {v!r} in bitwise '{op_name}' operation; treated as 0.", file=sys.stderr)
            return 0

    def term3(self, s, idx):
        """& (bitwise AND), but not && (logical AND, handled by term9)."""
        x, idx = self.term2(s, idx)
        while idx < len(s) and s[idx] == '&' and (idx + 1 >= len(s) or s[idx + 1] != '&'):
            t, idx = self.term2(s, idx + 1)
            x = self._safe_int(x, '&') & self._safe_int(t, '&')
        return x, idx

    def term4(self, s, idx):
        """| (bitwise OR), but not || (logical OR, handled by term10)."""
        x, idx = self.term3(s, idx)
        while idx < len(s) and s[idx] == '|' and (idx + 1 >= len(s) or s[idx + 1] != '|'):
            t, idx = self.term3(s, idx + 1)
            x = self._safe_int(x, '|') | self._safe_int(t, '|')
        return x, idx

    def term5(self, s, idx):
        """^ (bitwise XOR)."""
        x, idx = self.term4(s, idx)
        while idx < len(s) and s[idx] == '^':
            t, idx = self.term4(s, idx + 1)
            x = self._safe_int(x, '^') ^ self._safe_int(t, '^')
        return x, idx

    def term6(self, s, idx):
        """x'n : sign-extend x as if it were an n-bit signed value (used to
        turn a small captured field, e.g. a 5-bit displacement, into its
        correctly-signed full-width value before further arithmetic). Only
        triggers when a digit or '(' follows the "'", so a bare "'a'"
        character literal elsewhere in the expression isn't misread as this
        operator."""
        _SEXT_MAX_BITS = 128
        x, idx = self.term5(s, idx)
        while idx < len(s) and s[idx] == '\'':
            next_idx = idx + 1
            next_idx = StringUtils.skipspc(s, next_idx)
            if next_idx >= len(s) or (s[next_idx] not in DIGIT and s[next_idx] != '('):
                break
            t, idx = self.term5(s, idx + 1)
            try:
                x = int(x)
                t = int(t)
            except (ValueError, OverflowError):
                x = 0
                break
            if t <= 0:
                x = 0
            elif t > _SEXT_MAX_BITS:
                print(f" warning - sign-extension bit width {t} exceeds maximum {_SEXT_MAX_BITS}, result set to 0.", file=sys.stderr)
                x = 0
            else:
                x = (x & ~((~0) << t)) | ((~0) << t if (x >> (t - 1) & 1) else 0)
        return x, idx

    def term7(self, s, idx):
        """Comparison operators (<=, <, >=, >, ==, !=), each yielding 1/0."""
        x, idx = self.term6(s, idx)
        while idx < len(s):
            if StringUtils.q(s, '<=', idx):
                t, idx = self.term6(s, idx + 2)
                x = 1 if x <= t else 0
            elif s[idx] == '<':
                t, idx = self.term6(s, idx + 1)
                x = 1 if x < t else 0
            elif StringUtils.q(s, '>=', idx):
                t, idx = self.term6(s, idx + 2)
                x = 1 if x >= t else 0
            elif s[idx] == '>':
                t, idx = self.term6(s, idx + 1)
                x = 1 if x > t else 0
            elif StringUtils.q(s, '==', idx):
                t, idx = self.term6(s, idx + 2)
                x = 1 if x == t else 0
            elif StringUtils.q(s, '!=', idx):
                t, idx = self.term6(s, idx + 2)
                x = 1 if x != t else 0
            else:
                break
        return x, idx

    def term8(self, s, idx):
        """Placeholder level between term7 (comparisons) and term9 (&&).
        `not(expr)` used to be special-cased here, but that meant only
        operators ABOVE this level (&&, ||, ternary) could combine with its
        result; anything below (comparisons, +/-, etc.) is only ever invoked
        while parsing a fresh left-hand operand, so e.g. "not(0)+5" silently
        dropped the "+5". `not(...)` is now handled in factor1() instead,
        the base of the chain, so its result is an ordinary atom to every
        operator on either side. See ExpressionEvaluator's class docstring
        for the term0_0..term11 chain."""
        return self.term7(s, idx)

    def term9(self, s, idx):
        """&& (logical AND)."""
        x, idx = self.term8(s, idx)
        while idx < len(s) and StringUtils.q(s, '&&', idx):
            t, idx = self.term8(s, idx + 2)
            x = 1 if x and t else 0
        return x, idx

    def term10(self, s, idx):
        """|| (logical OR) -- lowest-precedence binary operator."""
        x, idx = self.term9(s, idx)
        while idx < len(s) and StringUtils.q(s, '||', idx):
            t, idx = self.term9(s, idx + 2)
            x = 1 if x or t else 0
        return x, idx

    def term11(self, s, idx):
        """cond ? true_expr : false_expr (ternary), the lowest-precedence
        construct and the only right-associative one (hence its own level
        recursing into itself for both branches).

        Both branches must actually be *parsed* to find where the whole
        ternary ends, regardless of which one the condition picks -- but
        evaluating the untaken branch can still have side effects (capturing
        pattern variables, flagging an undefined label, recording an ELF
        relocation reference), and those must not leak into the final
        result. So state.vars/error flags/ELF-tracking lists are snapshotted
        before evaluating the true branch, evaluated for both branches in
        turn, and finally *replaced* with whichever branch's post-evaluation
        state corresponds to the chosen result -- never merged, so the
        rejected branch's effects are fully discarded.
        """
        x, idx = self.term10(s, idx)
        if idx < len(s) and StringUtils.q(s, '?', idx):
            saved_vars              = self.state.vars[:]
            saved_err_undef         = self.state.error_undefined_label
            saved_err_conflict      = self.state.error_label_conflict
            saved_elf_refs_len      = len(self.state._elf_label_refs_seen)
            saved_elf_v2l           = dict(self.state._elf_var_to_label)

            t, idx = self.term11(s, idx + 1)
            vars_after_true         = self.state.vars[:]
            err_after_true          = self.state.error_undefined_label
            conflict_after_true     = self.state.error_label_conflict
            refs_after_true         = list(self.state._elf_label_refs_seen)
            v2l_after_true          = dict(self.state._elf_var_to_label)

            if idx < len(s) and StringUtils.q(s, ':', idx):
                self.state.vars                     = saved_vars[:]
                self.state.error_undefined_label    = saved_err_undef
                self.state.error_label_conflict     = saved_err_conflict
                del self.state._elf_label_refs_seen[saved_elf_refs_len:]
                self.state._elf_var_to_label        = dict(saved_elf_v2l)
                u, idx = self.term11(s, idx + 1)

                if x != 0:
                    self.state.vars                     = vars_after_true
                    self.state.error_undefined_label    = err_after_true
                    self.state.error_label_conflict     = conflict_after_true
                    self.state._elf_label_refs_seen     = refs_after_true
                    self.state._elf_var_to_label        = v2l_after_true
                    x = t
                else:
                    x = u
            else:
                if x != 0:
                    self.state.vars                     = vars_after_true
                    self.state.error_undefined_label    = err_after_true
                    self.state.error_label_conflict     = conflict_after_true
                    self.state._elf_label_refs_seen     = refs_after_true
                    self.state._elf_var_to_label        = v2l_after_true
                    x = t
                else:
                    self.state.vars                     = saved_vars
                    self.state.error_undefined_label    = saved_err_undef
                    self.state.error_label_conflict     = saved_err_conflict
                    del self.state._elf_label_refs_seen[saved_elf_refs_len:]
                    self.state._elf_var_to_label        = dict(saved_elf_v2l)
                    x = 0
        return x, idx

    def expression(self, s, idx):
        """Public entry point: parse one full expression starting at idx,
        guarding the whole term0-term11 recursive-descent chain against a
        RecursionError from pathologically deep/nested input (reported as an
        error instead of crashing the assembler)."""
        try:
            idx0 = StringUtils.skipspc(s, idx)
            x, idx0 = self.term11(s, idx0)
            return x, idx0
        except RecursionError:
            if self.state.should_report_errors():
                print(" error - expression nesting too deep (RecursionError).",
                      file=sys.stderr)
            return 0, idx

    def _terminate(self, s):
        """Ensure a NUL terminator is present, since several factor()/factor1()
        lookahead checks compare against chr(0) as an explicit "end of input"
        sentinel rather than checking len(s) everywhere."""
        if not s or s[-1] != chr(0):
            return s + chr(0)
        return s

    def expression_pat(self, s, idx):
        """Evaluate an expression in pattern-file context (EXP_PAT), where
        "!!!"/"!!!!" mean the VLIW slot-count/end-of-packet markers rather
        than being unrecognized tokens."""
        prev = self.state.expmode
        self.state.expmode = EXP_PAT
        try:
            return self.expression(self._terminate(s), idx)
        finally:
            self.state.expmode = prev

    def expression_asm(self, s, idx):
        """Evaluate an expression in assembly-source context (EXP_ASM)."""
        prev = self.state.expmode
        self.state.expmode = EXP_ASM
        try:
            return self.expression(self._terminate(s), idx)
        finally:
            self.state.expmode = prev

    def expression_esc(self, s, idx, stopchar):
        """Evaluate an expression that runs until an unbracketed occurrence
        of stopchar (used to find where a pattern's operand-capture
        expression ends when the stop character itself might also appear,
        legitimately, inside balanced ()/[] or the pattern file's OB/CB
        [[/]] escapes). A small stack of open-bracket characters tracks
        nesting depth; stopchar only actually terminates the expression when
        the stack is empty, i.e. we're not inside any bracket pair."""
        result = list(s[:idx])

        OPEN_TO_CLOSE = {'(': ')', '[': ']', OB: CB}
        CLOSE_CHARS   = set(OPEN_TO_CLOSE.values())

        stack = []

        for ch in s[idx:]:
            if not stack and ch == stopchar:
                result.append(chr(0))
                break
            elif ch in OPEN_TO_CLOSE:
                stack.append(ch)
                result.append(ch)
            elif ch in CLOSE_CHARS:
                if stack and OPEN_TO_CLOSE.get(stack[-1]) == ch:
                    stack.pop()
                    result.append(ch)
                else:
                    result.append(ch)
            else:
                result.append(ch)

        replaced = ''.join(result)
        return self.expression(self._terminate(replaced), idx)

    def expression_esc_float(self, s, idx, stopchar):
        prev_typ  = self.state.exp_typ
        prev_mode = self.state.expmode
        self.state.exp_typ = 'f'
        try:
            v, idx = self.expression_esc(s, idx, stopchar)
        finally:
            self.state.exp_typ  = prev_typ
            self.state.expmode  = prev_mode
        return (v, idx)


class BinaryWriter:
    """Accumulates assembled words in a sparse {position: value} buffer and,
    on flush(), writes them out as a flat raw binary file (the -b output
    path, as opposed to -o's ELF object output which is handled separately
    in Assembler.write_elf_obj()). Sparse storage lets .ORG jump the write
    position around freely; any positions never written stay at
    state.padding when flushed."""

    def __init__(self, state):
        self.state = state
        self._buffer = {}

    def _store(self, position, word_val):
        if self.state.bts <= 0:
            return
        if position < 0:
            return
        mask = (1 << self.state.bts) - 1
        self._buffer[position] = word_val & mask

    def flush(self):
        """Write the buffered words to state.outfile as a flat binary,
        filling any never-written word positions up to the highest position
        seen with state.padding. Guards against a pathologically large
        computed output size (e.g. from a mistaken huge .ORG address)."""
        if not self.state.outfile or not self._buffer:
            return

        if self.state.bts <= 0:
            print(f" warning - flush: bts={self.state.bts} is invalid (<=0); "
                  f"output file '{self.state.outfile}' will be empty.", file=sys.stderr)
            return

        valid_buffer = {k: v for k, v in self._buffer.items() if k >= 0}
        if not valid_buffer:
            return

        max_word_pos = max(valid_buffer.keys())

        word_bits = self.state.bts
        bytes_per_word = (word_bits + 7) // 8

        total_size = (max_word_pos + 1) * bytes_per_word

        if total_size <= 0:
            return

        _MAX_OUTPUT_BYTES = 1 << 30
        if total_size > _MAX_OUTPUT_BYTES:
            print(f" error - output size {total_size} bytes exceeds maximum {_MAX_OUTPUT_BYTES}. "
                  f"Check for incorrect .ORG or address values.",
                  file=__import__('sys').stderr)
            return

        pad_val = int(self.state.padding) & ((1 << word_bits) - 1)
        if pad_val != 0:
            tmp = pad_val
            if self.state.endian == 'little':
                pad_bytes = bytes([(tmp >> (8 * i)) & 0xff for i in range(bytes_per_word)])
            else:
                pad_bytes = bytes([(tmp >> (8 * (bytes_per_word - 1 - i))) & 0xff
                                   for i in range(bytes_per_word)])
            data = bytearray(pad_bytes * (max_word_pos + 1))
        else:
            data = bytearray(total_size)

        for pos, val in valid_buffer.items():
            base_idx = pos * bytes_per_word

            temp_val = val
            if self.state.endian == 'little':
                for i in range(bytes_per_word):
                    if base_idx + i < total_size:
                        data[base_idx + i] = temp_val & 0xff
                        temp_val >>= 8
            else:
                for i in range(bytes_per_word - 1, -1, -1):
                    if base_idx + i < total_size:
                        data[base_idx + i] = temp_val & 0xff
                        temp_val >>= 8

        with open(self.state.outfile, 'wb') as f:
            f.write(data)
        print(f"wrote raw binary {self.state.outfile} ({len(data)} bytes)", file=sys.stderr)

    def fwrite(self, position, x, prt):
        """Mask x to the current word width, optionally echo it in hex
        (verbose/-v output), and buffer it at `position`."""
        if self.state.bts <= 0:
            return 0
        mask = (1 << self.state.bts) - 1
        val = x & mask

        if prt:
            b = self.state.bts
            colm = (b + 3) // 4
            print(f" 0x{val:0{colm}x}", end='')

        self._store(position, val)
        return 1

    def outbin2(self, a, x):
        """Write a word without ever echoing it (used for internal/silent
        writes, e.g. .ORG's fill bytes)."""
        if self.state.should_report_errors():
            try:
                self.fwrite(a, int(x), 0)
            except (OverflowError, ValueError):
                if self.state.should_report_errors():
                    print(f" error - non-finite value {x!r} cannot be written as binary word.", file=sys.stderr)

    def outbin(self, a, x):
        """Write a word, echoing it in hex only when that's actually
        meaningful to show: interactive mode, or verbose Pass 2 (Pass 1 is
        just relaxation bookkeeping, and non-verbose Pass 2 is silent)."""
        if self.state.should_report_errors():
            _prt = 1 if ((self.state.pas == 2 and self.state.verbose) or self.state.pas == 0) else 0
            try:
                self.fwrite(a, int(x), _prt)
            except (OverflowError, ValueError):
                if self.state.should_report_errors():
                    print(f" error - non-finite value {x!r} cannot be written as binary word.", file=sys.stderr)

    def align_(self, addr):
        """Round addr up to the next multiple of state.align (no-op if
        already aligned or if alignment is disabled). Note: the caller is
        responsible for using a *section-relative* addr when the result
        needs to reflect actual alignment in the final output file across a
        section re-entry -- see AssemblyDirectiveProcessor.align_processing()."""
        if self.state.align <= 0:
            return addr
        a = addr % self.state.align
        if a == 0:
            return addr
        return addr + self.state.align - a


class DirectiveProcessor:
    """Handles pattern-file-level directives (`.setsym`/`.clearsym`/`.bits`/
    `.padding`/`.symbolc`/`.vliw`/`EPIC`/`.check`/`.clrcheck`).

    Each method here recognizes one directive by checking `i[0]` (the parsed
    field list for the pattern line) and returns False immediately if it
    doesn't match, so callers can chain `processor.foo(i) or processor.bar(i)
    or ...` to dispatch on the directive keyword.
    """

    def __init__(self, state, expr_eval, binary_writer, symbol_manager=None, parser=None):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer
        self.symbol_manager = symbol_manager
        self.parser = parser

    def add_avoiding_dup(self, l, e):
        """Append `e` to `l` unless it's already present (used for vliwset)."""
        if e not in l:
            l.append(e)
        return l

    def clear_symbol(self, i):
        """`.clearsym [name]` — remove one pattern-symbol, or all of them if no name given."""
        if len(i) == 0 or i[0] != '.clearsym':
            return False

        if len(i) >= 3 and i[2] != '':
            key = StringUtils.upper(i[2])
            self.state.symbols.pop(key, None)
        else:
            self.state.symbols = {}

        return True

    def set_symbol(self, i):
        """`.setsym name [value]` — define/overwrite a pattern-file symbol."""
        if len(i) == 0 or i[0] != '.setsym':
            return False

        # readpat() pads every directive line to a fixed 6-field list, and
        # for a line with only ONE `::`-separated argument it lands that
        # argument in i[2], not i[1] (its indexing is built for
        # pattern-definition lines, whose 2-field form is "mnemonic ::
        # encoding" with an implicit empty operand-syntax field in between).
        # So a name-only ".setsym::FOO" is a 2-field line with the name in
        # i[2]; only the 3-field ".setsym::FOO::value" form puts it in i[1].
        # Bugfix: this method used to always read the name from i[1] and
        # always evaluate i[2] as the value expression, so the name-only
        # form stored an empty-string key and reported "Label undefined"
        # for the name (misread as a value expression).
        if i[1]:
            key = StringUtils.upper(i[1])
            value_field = i[2]
        elif i[2]:
            key = StringUtils.upper(i[2])
            value_field = ''
        else:
            print(" error - .setsym directive requires at least a symbol name", file=sys.stderr)
            self.state.had_error = True
            return False

        if value_field:
            v, idx = self.expr_eval.expression_pat(value_field, 0)
        else:
            v = 0
        self.state.symbols[key] = v
        return True

    def bits(self, i):
        """`.bits [big|little] [width]` — set endianness and/or default word width."""
        if len(i) == 0 or i[0] != '.bits':
            return False

        if len(i) >= 2:
            if i[1].lower() == 'big':
                self.state.endian = 'big'
            elif i[1].lower() == 'little':
                self.state.endian = 'little'

        v = None
        if len(i) >= 3:
            v, idx = self.expr_eval.expression_pat(i[2], 0)
        elif len(i) >= 2 and i[1].lower() not in ('big', 'little'):
            v, idx = self.expr_eval.expression_pat(i[1], 0)
        if v is not None:
            try:
                self.state.bts = int(v)
            except (OverflowError, ValueError):
                print(" error - .bits: non-finite bit width value.", file=sys.stderr)
                self.state.had_error = True
        return True

    def paddingp(self, i):
        """`.padding value` — set the fill byte/word used to pad unemitted bits."""
        if len(i) == 0 or i[0] != '.padding':
            return False

        if len(i) >= 3 and i[2] != '':
            v, idx = self.expr_eval.expression_pat(i[2], 0)
        elif len(i) >= 2 and i[1] != '':
            v, idx = self.expr_eval.expression_pat(i[1], 0)
        else:
            v = 0
        try:
            self.state.padding = int(v)
        except (OverflowError, ValueError):
            print(" error - .padding: non-finite or invalid value; padding unchanged.", file=sys.stderr)
            self.state.had_error = True
        return True

    def symbolc(self, i):
        """`.symbolc extrachars` — extend the character set allowed in symbol words."""
        if len(i) == 0 or i[0] != '.symbolc':
            return False

        if len(i) > 2 and i[2] != '':
            self.state.swordchars = ALPHABET + DIGIT + i[2]
        return True

    def vliwp(self, i):
        """`.vliw vliwbits vliwinstbits vliwtemplatebits nop_value` — declare a VLIW/EPIC
        target's packet width, per-slot instruction width, template-field width, and the
        NOP filler bit pattern (converted here to a little-endian byte list)."""
        if len(i) == 0 or i[0] != ".vliw":
            return False

        if len(i) < 5:
            print(f" error - .vliw directive requires 4 parameters (vliwbits, vliwinstbits, vliwtemplatebits, nop_value), got {len(i) - 1}", file=sys.stderr)
            return False

        v1, idx = self.expr_eval.expression_pat(i[1], 0)
        v2, idx = self.expr_eval.expression_pat(i[2], 0)
        v3, idx = self.expr_eval.expression_pat(i[3], 0)
        v4, idx = self.expr_eval.expression_pat(i[4], 0)

        try:
            self.state.vliwbits        = int(v1)
            self.state.vliwinstbits    = int(v2)
            self.state.vliwtemplatebits = int(v3)
        except (OverflowError, ValueError):
            print(" error - .vliw: non-finite parameter value.", file=sys.stderr)
            self.state.had_error = True
            # Bugfix: this directive line (i[0] == '.vliw') was already
            # claimed above; returning False here (instead of True, like
            # every other directive's error path) told the caller's dispatch
            # chain this line was NOT handled, so it fell through and got
            # retried as an ordinary instruction pattern against every
            # subsequent source line for the rest of the assembly --
            # spamming this error once per source line instead of once.
            return True

        _VLIW_INSTBITS_MAX = 8192
        if not (0 <= self.state.vliwinstbits <= _VLIW_INSTBITS_MAX):
            print(f" error - .vliw: vliwinstbits {self.state.vliwinstbits} is out of range "
                  f"(must be 0-{_VLIW_INSTBITS_MAX}).", file=sys.stderr)
            self.state.had_error = True
            return True

        self.state.vliwflag = True

        l = []
        for _byte_idx in range(self.state.vliwinstbits // 8 + (0 if self.state.vliwinstbits % 8 == 0 else 1)):
            l += [v4 & 0xff]
            v4 >>= 8
        self.state.vliwnop = l
        return True

    def epic(self, i):
        """`EPIC slot_indices pattern` — register an EPIC-style multi-slot pattern:
        `slot_indices` is a comma-separated list of expressions giving which
        packet slot(s) the pattern occupies; `pattern` is the mnemonic syntax
        for that slot combination. Entries accumulate in `state.vliwset`."""
        if len(i) == 0 or StringUtils.upper(i[0]) != "EPIC":
            return False

        if len(i) <= 1 or i[1] == '':
            return False

        if len(i) < 3:
            print(f" error - EPIC directive requires 2 parameters (indices, pattern), got {len(i) - 1}", file=sys.stderr)
            self.state.had_error = True
            return False

        s = i[1]
        idxs = []
        idx = 0
        while True:
            v, idx = self.expr_eval.expression_pat(s, idx)
            idxs += [v]
            if idx < len(s) and s[idx] == ',':
                idx += 1
                continue
            break

        s2 = i[2]
        self.state.vliwset = self.add_avoiding_dup(self.state.vliwset, [idxs, s2])
        return True

    def error(self, s):
        """Evaluate a pattern-file `.ERROR condition;code, ...` field: for each
        `condition;code` pair, if `condition` is truthy and errors are currently
        being reported (see `AssemblerState.should_report_errors`), print the
        diagnostic (looked up by code in `ERRORS`) and record it as triggered.
        Returns (triggered, last_error_code)."""
        ss = s.replace(' ', '')
        if ss == "":
            return False, 0

        s += chr(0)
        idx = 0
        error_code = 0
        triggered = False

        while True:
            ch = s[idx] if idx < len(s) else chr(0)
            if ch == chr(0):
                break
            if ch == ',':
                idx += 1
                continue

            idx_before = idx
            prev_typ = self.expr_eval.state.exp_typ
            self.expr_eval.state.exp_typ = 'f'
            try:
                u, idxn = self.expr_eval.expression_pat(s, idx)
                idx = idxn
                if idx < len(s) and s[idx] == ';':
                    idx += 1
                t, idx = self.expr_eval.expression_pat(s, idx)
            finally:
                self.expr_eval.state.exp_typ = prev_typ

            if idx <= idx_before:
                break

            if (self.state.should_report_errors()) and u:
                try:
                    t_int = int(t)
                except (OverflowError, ValueError):
                    t_int = 0
                print(f"Line {self.state.ln} Error code {t_int} ", end="", file=sys.stderr)
                if 0 <= t_int < len(ERRORS):
                    print(f"{ERRORS[t_int]}", end='', file=sys.stderr)
                print(": ", file=sys.stderr)
                error_code = t_int
                triggered = True

        return triggered, error_code

    def check_processing(self, i):
        """`.check var [ALLOWED,SYMS,...]` — restrict which `.setsym` symbol
        names the lower-case pattern-template letter `var` (a *bare* operand
        letter matched directly against a source symbol word, e.g. the `a`
        in a template like `MOV a,b` -- NOT a `!x`-style captured
        expression, which can evaluate to an arbitrary value and has no
        single "symbol name" to check against a list; see the sole
        enforcement site, ExpressionEvaluator/PatternMatcher's `elif a in
        LOWER:` branch) may match to. An empty list means "no restriction
        has been set" is not the same as "any symbol", callers consult
        `state.check_constraints` directly."""
        if len(i) == 0 or i[0] != '.check':
            return False
        # Same readpat() 2-field-vs-3-field indexing quirk as .setsym (see
        # its comment above): a var-only ".check::c" line puts "c" in i[2],
        # not i[1] -- only the 3-field ".check::c::LIST" form puts the var
        # in i[1]. Bugfix: this method used to always read the var from
        # i[1], so the list-less form always hit the "not specified" error.
        if i[1].strip():
            var_field, syms_field = i[1], i[2]
        elif i[2].strip():
            var_field, syms_field = i[2], ''
        else:
            print(" error - .check: variable name is not specified.", file=sys.stderr)
            self.state.had_error = True
            return True
        var = var_field.strip().lower()
        if len(var) != 1 or var not in LOWER:
            print(f" error - .check: variable should be a lower case letter ('{var_field}').",
                  file=sys.stderr)
            self.state.had_error = True
            return True
        syms = []
        if syms_field:
            syms = [s.strip().upper() for s in syms_field.split(',') if s.strip()]
        self.state.check_constraints[var] = syms
        return True

    def clrcheck_processing(self, i):
        """`.clrcheck [var]` — remove one variable's `.check` restriction, or all of them."""
        if len(i) == 0 or i[0] != '.clrcheck':
            return False
        var_field = i[2].strip() if len(i) >= 3 and i[2] else ''
        if var_field:
            var = var_field.lower()
            if len(var) == 1 and var in LOWER:
                self.state.check_constraints.pop(var, None)
            else:
                print(f" error - .clrcheck: variable should be a lower case letter ('{var_field}').",
                      file=sys.stderr)
                self.state.had_error = True
        else:
            self.state.check_constraints.clear()
        return True


class PatternMatcher:
    """Matches one source-line-fragment `s` against one pattern-file syntax
    template `t`, binding pattern variables (`!x`) to symbols/expression values
    as it goes. `t` uses uppercase letters as literal-but-case-insensitive
    text, lowercase letters as symbol-reference variables, `!x` as
    expression-capturing variables (with `!Fx`/`!Dx`/`!Qx` float variants and
    `!!x` for a "raw factor, no operators" capture), and `[[...]]` (rewritten
    to OB/CB sentinels) to mark optional groups tried both present and absent.

    `last_score`/`last_match_score` record `(n_expr, -n_lit, n_sym)` for the
    most recent successful match so callers can prefer the pattern with the
    most literal text (fewest captured/least ambiguous) when several patterns
    match the same source line.
    """

    def __init__(self, state, expr_eval, var_manager, symbol_manager, parser):
        self.state = state
        self.expr_eval = expr_eval
        self.var_manager = var_manager
        self.symbol_manager = symbol_manager
        self.parser = parser
        self.last_score = None
        self.last_match_score = None

    def remove_brackets(self, s, l):
        """Given optional-group serial numbers `l` (1-based, in first-seen
        order of OB), blank out those `[[...]]` groups' contents in `s` —
        used by `match0` to try each present/absent combination of optional
        groups without re-parsing the bracket nesting each time."""
        serial = 0
        stack = []
        bracket_pairs = {}

        for i, char in enumerate(s):
            if char == OB:
                serial += 1
                stack.append((serial, i))
            elif char == CB:
                if stack:
                    ser, open_pos = stack.pop()
                    bracket_pairs[ser] = (open_pos, i)

        result = list(s)
        for index in l:
            if index in bracket_pairs:
                start_pos, end_pos = bracket_pairs[index]
                for j in range(start_pos, end_pos + 1):
                    result[j] = ''

        return ''.join(result)

    def match(self, s, t):
        """Try to match source fragment `s` against pattern `t` (with any
        remaining OB/CB optional-group markers stripped — `match0` has already
        decided which groups are present). Walks both strings in lockstep:
        uppercase template chars require a case-insensitive literal match,
        lowercase chars consume a symbol word via `get_symbol_word`, `!x`
        (and its `!Fx`/`!Dx`/`!Qx`/`!!x` variants) consumes an expression via
        the appropriate `ExpressionEvaluator` entry point, and any other char
        must match literally. A "word break" check (`word_break`) rejects
        matches where a literal/keyword match would run together with an
        adjacent alnum sequence that came from a different template atom,
        avoiding e.g. matching "MOV" as a prefix of "MOVQ". Returns True (with
        `last_score` set) on a full match to end-of-string, False otherwise —
        any variable bindings made along a failed path are the caller's
        (`match0`'s) responsibility to roll back."""
        self.state.deb1 = s
        self.state.deb2 = t

        n_expr = 0
        n_sym = 0
        n_lit = 0

        t = t.replace(OB, '').replace(CB, '')
        idx_s = 0
        idx_t = 0
        idx_s = StringUtils.skipspc(s, idx_s)
        idx_t = StringUtils.skipspc(t, idx_t)
        s += chr(0)
        t += chr(0)

        prev_alnum = False

        while True:

            s_sp = idx_s < len(s) and s[idx_s] in ' \t'
            t_sp = idx_t < len(t) and t[idx_t] in ' \t'
            idx_s = StringUtils.skipspc(s, idx_s)
            idx_t = StringUtils.skipspc(t, idx_t)

            word_break = s_sp and not t_sp
            b = s[idx_s]
            a = t[idx_t]

            if a == chr(0) and b == chr(0):
                self.last_score = (n_expr, -n_lit, n_sym)
                return True

            if a == '\\':
                idx_t += 1
                if idx_t < len(t) and t[idx_t] == b:
                    lit_alnum = t[idx_t].isalnum()
                    if lit_alnum and prev_alnum and word_break:
                        return False
                    idx_t += 1
                    idx_s += 1
                    n_lit += 1
                    prev_alnum = lit_alnum
                    continue
                else:
                    return False
            elif a in CAPITAL:
                if a == b.upper():

                    if prev_alnum and word_break:
                        return False
                    idx_s += 1
                    idx_t += 1
                    n_lit += 1
                    prev_alnum = True
                    continue
                else:
                    return False
            elif a == '!':
                prev_alnum = False
                n_expr += 1
                idx_t += 1
                if idx_t >= len(t):
                    return False
                a = t[idx_t]
                idx_t += 1
                if a == chr(0):
                    return False
                if a == 'F':
                    # !Fx: capture a float32-encoded expression into variable x.
                    if idx_t >= len(t):
                        return False
                    a = t[idx_t]
                    if a == chr(0) or a not in LOWER:
                        return False
                    idx_t = StringUtils.skipspc(t, idx_t + 1)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t += 1
                        stopchar = t[idx_t] if idx_t < len(t) else chr(0)
                        idx_t += 1
                    else:
                        stopchar = chr(0)

                    try:
                        v, idx_s = self.expr_eval.expression_esc_float(s, idx_s, stopchar)
                    finally:
                        self.state._elf_capturing_var = None
                    try:
                        v = float(v)
                        v = int.from_bytes(struct.pack('>f', v), "big")
                    except (OverflowError, ValueError, struct.error):
                        if self.state.should_report_errors():
                            print(" error - !F: cannot convert value to float32; using 0.", file=sys.stderr)
                        v = 0
                    self.var_manager.put(a, v)
                    if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                        idx_s += 1
                    continue
                elif a == 'D':
                    # !Dx: capture a float64-encoded expression into variable x.
                    if idx_t >= len(t):
                        return False
                    a = t[idx_t]
                    if a == chr(0) or a not in LOWER:
                        return False
                    idx_t = StringUtils.skipspc(t, idx_t + 1)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t += 1
                        stopchar = t[idx_t] if idx_t < len(t) else chr(0)
                        idx_t += 1
                    else:
                        stopchar = chr(0)

                    try:
                        v, idx_s = self.expr_eval.expression_esc_float(s, idx_s, stopchar)
                    finally:
                        self.state._elf_capturing_var = None
                    try:
                        v = float(v)
                        v = int.from_bytes(struct.pack('>d', v), "big")
                    except (OverflowError, ValueError, struct.error):
                        if self.state.should_report_errors():
                            print(" error - !D: cannot convert value to float64; using 0.", file=sys.stderr)
                        v = 0
                    self.var_manager.put(a, v)
                    if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                        idx_s += 1
                    continue
                elif a == 'Q':
                    # !Qx: capture as IEEE754 128-bit ("quad") float, via decimal_eval_expr
                    # on the raw source text (not the numeric result) for full precision.
                    if idx_t >= len(t):
                        return False
                    a = t[idx_t]
                    if a == chr(0) or a not in LOWER:
                        return False
                    idx_t = StringUtils.skipspc(t, idx_t + 1)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t += 1
                        stopchar = t[idx_t] if idx_t < len(t) else chr(0)
                        idx_t += 1
                    else:
                        stopchar = chr(0)

                    idx_s_q_start = idx_s

                    try:
                        v, idx_s_after = self.expr_eval.expression_esc_float(s, idx_s, stopchar)
                    finally:
                        self.state._elf_capturing_var = None

                    raw_text = s[idx_s_q_start:idx_s_after]
                    if stopchar != chr(0) and raw_text.endswith(stopchar):
                        raw_text = raw_text[:-1]
                    raw_text = raw_text.strip()

                    if raw_text.startswith('qad{') and raw_text.endswith('}'):
                        raw_text = raw_text[4:-1].strip()

                    try:
                        h = IEEE754Converter.decimal_eval_expr(raw_text)
                    except (ValueError, ZeroDivisionError):
                        if isinstance(v, int) or (
                                isinstance(v, float) and v.is_integer()):
                            h = IEEE754Converter.decimal_to_ieee754_128bit_hex(
                                    str(int(v)))
                        else:
                            h = IEEE754Converter.decimal_to_ieee754_128bit_hex(
                                    repr(float(v)))

                    x = int(h, 16)
                    self.var_manager.put(a, x)
                    idx_s = idx_s_after
                    if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                        idx_s += 1
                    continue
                elif a == '!':
                    # !!x: capture a single "factor" only (no binary operators) —
                    # used where the pattern needs to stop before an operator that
                    # is itself part of the surrounding template, not the operand.
                    if idx_t >= len(t):
                        return False
                    a = t[idx_t]
                    if a == chr(0) or a not in LOWER:
                        return False
                    idx_t += 1
                    self.state._elf_capturing_var = a
                    try:
                        v, idx_s = self.expr_eval.factor(s, idx_s)
                    finally:
                        self.state._elf_capturing_var = None
                    self.var_manager.put(a, v)
                    continue
                else:
                    # !x: capture a full expression into variable x.
                    if a == chr(0) or a not in LOWER:
                        return False
                    idx_t = StringUtils.skipspc(t, idx_t)
                    if idx_t < len(t) and t[idx_t] == '\\':
                        idx_t += 1
                        stopchar = t[idx_t] if idx_t < len(t) else chr(0)
                        idx_t += 1
                    else:
                        stopchar = chr(0)

                    self.state._elf_capturing_var = a
                    try:
                        v, idx_s = self.expr_eval.expression_esc(s, idx_s, stopchar)
                    finally:
                        self.state._elf_capturing_var = None
                    self.var_manager.put(a, v)
                    if stopchar != chr(0) and idx_s < len(s) and s[idx_s] == stopchar:
                        idx_s += 1
                    continue
            elif a in LOWER:
                prev_alnum = False
                idx_t += 1
                prev_idx_s = idx_s
                w, idx_s = self.parser.get_symbol_word(s, idx_s)
                v = self.symbol_manager.get(w)
                if v == "":
                    return False
                if a in self.state.check_constraints and w not in self.state.check_constraints[a]:
                    return False
                if idx_s == prev_idx_s:
                    return False
                self.var_manager.put(a, v)
                n_sym += 1
                continue
            elif a == b:

                lit_alnum = a.isalnum()
                if lit_alnum and prev_alnum and word_break:
                    return False
                idx_t += 1
                idx_s += 1
                n_lit += 1
                prev_alnum = lit_alnum
                continue
            else:
                return False

    _MAX_COMBINATIONS = 1 << 16

    def match0(self, s, t):
        """Entry point for matching: expands `[[...]]` optional groups to
        OB/CB, then tries every subset of groups present/absent (largest
        subsets first, so the most literal-text match wins ties), calling
        `match()` for each candidate and restoring `state.vars`/ELF-tracking
        on failure. Bails out (treats as non-matching) if the group count
        exceeds `_MAX_OPT_GROUPS` or the combination budget `_MAX_COMBINATIONS`
        is exceeded, to keep pathological patterns from hanging the assembler."""
        t = t.replace('[[', OB).replace(']]', CB)
        cnt = t.count(OB)
        sl = [_ + 1 for _ in range(cnt)]

        _MAX_OPT_GROUPS = 20
        if cnt > _MAX_OPT_GROUPS:
            if self.state.should_report_errors():
                print(f" warning - pattern has {cnt} optional groups (max {_MAX_OPT_GROUPS}); "
                      f"first {_MAX_OPT_GROUPS} are treated as optional, "
                      f"remainder are always included.", file=sys.stderr)
            sl = sl[:_MAX_OPT_GROUPS]
            cnt = _MAX_OPT_GROUPS

        _tried = 0
        for i in range(len(sl) + 1):

            for j in itertools.combinations(sl, i):
                _tried += 1
                if _tried > self._MAX_COMBINATIONS:

                    _warn_key = (getattr(self.state, 'current_file', None),
                                 getattr(self.state, 'ln', None), t)
                    if (self.state.should_report_errors()
                            and _warn_key not in self.state._combo_budget_warned):
                        self.state._combo_budget_warned.add(_warn_key)
                        print(f" warning - a pattern with {cnt} optional group(s) exceeded the "
                              f"{self._MAX_COMBINATIONS}-combination match budget and was treated "
                              f"as non-matching; consider splitting it into multiple explicit "
                              f"pattern entries.", file=sys.stderr)
                    return False
                lt = self.remove_brackets(t, list(j))
                saved_vars = self.state.vars[:]
                saved_refs_len = len(self.state._elf_label_refs_seen)
                saved_v2l      = dict(self.state._elf_var_to_label)
                if self.match(s, lt):
                    self.last_match_score = self.last_score
                    return True
                self.state.vars = saved_vars
                del self.state._elf_label_refs_seen[saved_refs_len:]
                self.state._elf_var_to_label = saved_v2l
        return False


class PatternFileReader:
    """Reads a `.axx` pattern file into a list of 6-field pattern-line records
    (`[mnemonic, size_field, syntax, object_field, extra1, extra2]`), handling
    `.INCLUDE` recursively with cycle/depth protection."""

    def __init__(self, parser):
        self.parser = parser

    def readpat(self, fn, base_dir=None, _depth=0, _chain=None):
        """Read and parse pattern file `fn`. `_chain` is the set of already-open
        (realpath-resolved) files on the current .INCLUDE stack, used to detect
        cycles; `_depth` caps recursion depth independently as a backstop."""
        if fn == '':
            return []

        _MAX_PAT_DEPTH = 50
        if _depth > _MAX_PAT_DEPTH:
            print(f" error - pattern .INCLUDE nesting exceeds {_MAX_PAT_DEPTH}: '{fn}'", file=sys.stderr)
            return []

        if base_dir and not os.path.isabs(fn):
            fn = os.path.join(base_dir, fn)

        _real = os.path.realpath(fn)
        if _chain is None:
            _chain = frozenset()
        if _real in _chain:
            print(f" error - circular pattern .INCLUDE detected: '{fn}' "
                  f"(already in include chain). Skipped.", file=sys.stderr)
            return []
        _chain = _chain | {_real}

        this_dir = os.path.dirname(os.path.abspath(fn))

        p = []
        w = []

        with open(fn, "rt", encoding="utf-8") as f:
            while True:
                l = f.readline()
                if not l:
                    break

                l = StringUtils.remove_comment(l)
                l = l.replace('\t', ' ')
                l = l.replace(chr(13), '')
                l = l.replace('\n', '')
                l = StringUtils.reduce_spaces(l)

                ww = self.include_pat(l, this_dir, _depth=_depth + 1, _chain=_chain)
                if ww is not None:
                    w = w + ww
                    continue
                else:
                    r = []
                    idx = 0
                    while True:
                        s, idx = self.parser.get_params1(l, idx)
                        r += [s]
                        if len(l) <= idx:
                            break
                    l = r

                    if len(l) == 1:
                        p = [l[0], '', '', '', '', '']
                    elif len(l) == 2:
                        p = [l[0], '', l[1], '', '', '']
                    elif len(l) == 3:
                        p = [l[0], l[1], l[2], '', '', '']
                    elif len(l) == 4:
                        p = [l[0], l[1], l[2], l[3], '', '']
                    elif len(l) == 5:
                        p = [l[0], l[1], l[2], l[3], l[4], '']
                    elif len(l) == 6:
                        p = [l[0], l[1], l[2], l[3], l[4], l[5]]
                    else:
                        print(f" warning - pattern line has more than 6 fields "
                              f"(extra fields ignored): {l[6:]!r}", file=sys.stderr)
                        p = [l[0], l[1], l[2], l[3], l[4], l[5]]
                    w.append(p)

        return w

    def include_pat(self, l, base_dir=None, _depth=0, _chain=None):
        """If line `l` is a `.INCLUDE "file"` directive, recursively read and
        return that file's pattern lines; otherwise return None so the caller
        parses `l` as an ordinary pattern-file line."""
        idx = StringUtils.skipspc(l, 0)
        i = l[idx:idx + 8]
        i = i.upper()
        if i != ".INCLUDE":
            return None
        s = StringUtils.get_string(l[idx + 8:])
        if s == "":
            raw = l[idx + 8:].strip()
            if raw:
                fallback, _ = StringUtils.get_param_to_spc(raw, 0)
                if fallback:
                    import sys as _sys
                    print(f" warning - .INCLUDE filename not quoted: {fallback!r}. "
                          "Please use double quotes.", file=_sys.stderr)
                    s = fallback
                else:
                    print(f" error - .INCLUDE directive has no filename: {l!r}", file=sys.stderr)
                    return []
            else:
                print(f" error - .INCLUDE directive has no filename: {l!r}", file=sys.stderr)
                return []
        w = self.readpat(s, base_dir, _depth=_depth, _chain=_chain)
        return w


class ObjectGenerator:
    """Turns a matched pattern's object-code field (the comma-separated list of
    expressions describing one instruction's encoded words) into a list of
    integer word values, expanding the `%%`/`%0` auto-index and `@@[n,...]`
    repeat-group shorthands first."""

    def __init__(self, state, expr_eval, binary_writer):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer

    def replace_percent_with_index(self, s):
        """Replace successive `%%` occurrences with 0,1,2,... (an auto-incrementing
        word index, e.g. for `%%*8` byte-offset fields); `%0` resets the counter."""
        count = 0
        result = []
        i = 0
        while i < len(s):
            if i + 1 < len(s) and s[i:i + 2] == '%%':
                result.append(str(count))
                count += 1
                i += 2
            elif i + 1 < len(s) and s[i:i + 2] == "%0":
                count = 0
                i += 2
            else:
                result.append(s[i])
                i += 1
        return ''.join(result)

    def e_p(self, pattern):
        """Expand `@@[count_expr, repeated_pattern]` groups by evaluating
        `count_expr` and emitting `repeated_pattern` that many times, comma-
        joined, in place of the group (capped at `_N_MAX` to guard against a
        runaway repeat count). Returns `(expanded_string, is_all_whitespace)`;
        the second value tells `makeobj` that a `z`-count of 0 (or a field
        that expanded to nothing) means "emit no words for this instruction"."""
        result = []
        has_content = False
        i = 0
        while i < len(pattern):
            if i + 3 <= len(pattern) and pattern[i:i + 3] == '@@[':
                i += 3
                depth = 1
                expr_start = i
                comma_pos = -1

                while i < len(pattern) and depth > 0:
                    if pattern[i] == '[':
                        depth += 1
                    elif pattern[i] == ']':
                        depth -= 1
                        if depth == 0:
                            break
                    elif pattern[i] == ',' and depth == 1 and comma_pos == -1:
                        comma_pos = i
                    i += 1

                if comma_pos >= 0 and comma_pos >= expr_start:
                    expr = pattern[expr_start:comma_pos]
                    rep_pattern = pattern[comma_pos + 1:i]

                    self.state.error_undefined_label = False
                    n, idx = self.expr_eval.expression_pat(expr, 0)
                    _N_MAX = 1 << 24
                    if self.state.error_undefined_label:
                        n = 0
                    try:
                        n_int = int(n)
                    except (ValueError, OverflowError):
                        n_int = 0
                    if n_int > _N_MAX:
                        if self.state.should_report_errors():
                            print(f" error - @@[n,...]: repeat count {n_int} exceeds maximum {_N_MAX}.", file=sys.stderr)
                        n_int = 0
                    if n_int > 0:
                        n = n_int
                        has_content = True
                        for j in range(int(n)):
                            if j > 0:
                                result.append(',')
                            result.append(rep_pattern)

                    i += 1
                else:
                    result.append('@@[')
                    has_content = True
            else:
                result.append(pattern[i])
                has_content = True
                i += 1

        return ''.join(result), not has_content

    def makeobj(self, s):
        """Evaluate a matched pattern's object-code field `s` (comma-separated
        expressions, `@@[]`/`%%` shorthand already handled by callers via `e_p`/
        `replace_percent_with_index`) into a list of integer word values, one
        per comma-separated expression. Sets `state._in_binary_list` for the
        duration so `LabelManager`/relocation-tracking code knows it's encoding
        real instruction bytes (see `LabelManager.get_value` and the ELF addend
        machinery, which behave differently outside this context). A leading
        `;` on a sub-expression makes that word conditional: if it evaluates to
        0, the word (and any relocation reference recorded for it) is dropped
        rather than emitted — used by patterns that only emit an optional
        prefix/suffix word when its value is nonzero."""
        s, z = self.e_p(s)
        s = self.replace_percent_with_index(s)

        s += chr(0)
        idx = 0
        objl = []

        if z:
            return objl

        self.state._in_binary_list = True
        # Bugfix: this used to unconditionally reset error_undefined_label
        # to False here, discarding any "undefined label" status the
        # caller had already established BEFORE calling makeobj() -- in
        # particular, a `!x`-captured pattern variable's value is computed
        # once during trial pattern-matching (get_value() calls happen
        # there, not here), so if that capture referenced an undefined
        # label, the only trace of it is the error_undefined_label flag the
        # caller carries into this call. Save it and OR it back in once
        # this call's own (correctly self-contained, comma-word-list-local)
        # tracking is done, instead of just dropping it on the floor.
        _prior_undef = self.state.error_undefined_label
        self.state.error_undefined_label = False
        try:
            while True:
                if idx >= len(s) or s[idx] == chr(0):
                    break

                if s[idx] == ',':
                    idx += 1
                    continue

                semicolon = False
                if s[idx] == ';':
                    semicolon = True
                    idx += 1

                self.state._elf_current_word_idx = len(objl)

                if self.state.pas == 1:
                    self.state._pass1_size_mode = True
                x, idx = self.expr_eval.expression_pat(s, idx)
                if self.state.pas == 1:
                    self.state._pass1_size_mode = False
                    self.state.error_undefined_label = False

                if not semicolon or x != 0:
                    objl += [x]
                elif semicolon:
                    self.state._elf_label_refs_seen = [
                        e for e in self.state._elf_label_refs_seen
                        if e[2] != self.state._elf_current_word_idx
                    ]

                if idx < len(s) and s[idx] == ',':
                    idx += 1
                    continue
                break
        finally:
            self.state._elf_current_word_idx = -1
            self.state._in_binary_list = False
            if self.state.pas == 1:
                self.state._pass1_size_mode = False
            self.state.error_undefined_label = self.state.error_undefined_label or _prior_undef

        return objl


class VLIWProcessor:
    """Assembles one VLIW/EPIC packet: a base instruction plus zero or more
    `!!`-separated additional slot instructions on the same source line,
    packed together with a template field per `.vliw`'s configured widths."""

    def __init__(self, state, expr_eval, binary_writer):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer

    def vliwprocess(self, line, idxs, objl, flag, idx, lineassemble2_func):
        """`objl`/`idxs`/`flag` are the already-assembled first slot's result;
        `idx` points just past it in `line`. Repeatedly consume `!!<instr>`
        slot separators (assembling each via `lineassemble2_func`, the
        `Assembler`'s own line-matching entry point, so slots use the exact
        same pattern-matching path as top-level instructions) until `!!!!`
        (marks the packet's last slot, stop-bit) or no more `!!` is found.
        Then looks up the matching `EPIC` slot-combination pattern (by the
        exact list of per-slot pattern indices used) to get this packet's
        template-field value, packs all slots' words into `vliwinstbits`-wide
        instruction fields (padding any leftover slots with `vliwnop`),
        combines them with the template per `vliwtemplatebits`'s sign (negative
        means template occupies the high bits), and emits the whole packet
        (`vliwbits` wide) to the output. Returns False (with a diagnostic) on
        any slot-assembly failure or config inconsistency."""
        objs = [objl]
        idxlst = [idxs]
        self.state.vliwstop = 0

        while True:
            idx = StringUtils.skipspc(line, idx)
            if idx + 4 <= len(line) and line[idx:idx + 4] == '!!!!':
                idx += 4
                self.state.vliwstop = 1
                continue
            elif idx + 2 <= len(line) and line[idx:idx + 2] == '!!':
                idx += 2

                _slot_peek = line[idx:].lstrip()
                if _slot_peek.startswith('.'):
                    if self.state.should_report_errors():
                        print(" error - directives (e.g. .section/.endsection/.INCLUDE) "
                              "are not allowed inside VLIW slots (the packet's PC has not "
                              "advanced yet at this point in the packet).", file=sys.stderr)
                    return False
                idxs, objl, flag, idx = lineassemble2_func(line, idx)
                if not flag:
                    return False
                objs += [objl]
                idxlst += [idxs]
                continue
            else:
                break

        if self.state.vliwtemplatebits == 0:
            self.state.vliwset = [[[0], "0"]]

        vbits = abs(self.state.vliwbits)

        if self.state.vliwinstbits == 0:
            if self.state.should_report_errors():
                print(" error - vliwinstbits is zero; cannot compute instruction slots.", file=sys.stderr)
            return False
        for k in self.state.vliwset:
            if list(k[0]) == list(idxlst) or self.state.vliwtemplatebits == 0:
                im = 2 ** self.state.vliwinstbits - 1
                tm = 2 ** abs(self.state.vliwtemplatebits) - 1
                pm = 2 ** vbits - 1
                x, idx = self.expr_eval.expression_pat(k[1], 0)
                templ = x & tm

                values = []
                ibyte = self.state.vliwinstbits // 8 + (0 if self.state.vliwinstbits % 8 == 0 else 1)
                noi = (vbits - abs(self.state.vliwtemplatebits)) // self.state.vliwinstbits

                if noi <= 0:
                    if self.state.should_report_errors():
                        print(f" error - .vliw: vliwtemplatebits ({self.state.vliwtemplatebits}) "
                              f"leaves no room for instruction slots in a {vbits}-bit packet "
                              f"(vliwinstbits={self.state.vliwinstbits}).", file=sys.stderr)
                    return False

                for j in objs:
                    for m in j:
                        values += [m]

                target_len = ibyte * noi
                if len(values) > target_len:
                    if self.state.should_report_errors():
                        print(f"warning-VLIW:{len(values)} values exceed slot capacity {target_len},truncating.", file=sys.stderr)
                    values = values[:target_len]
                else:
                    _deficit = target_len - len(values)
                    _full_nops, _remainder = divmod(_deficit, ibyte) if ibyte > 0 else (0, _deficit)
                    for _ in range(_full_nops):
                        values += self.state.vliwnop
                    if _remainder > 0:
                        values += (self.state.vliwnop + [0] * _remainder)[:_remainder]

                v1 = []
                cnt = 0

                for j in range(noi):
                    vv = 0
                    if self.state.endian == 'little':
                        for i in range(ibyte):
                            if len(values) > cnt:
                                vv |= (values[cnt] & 0xff) << (8 * i)
                            cnt += 1
                    else:
                        for i in range(ibyte):
                            vv <<= 8
                            if len(values) > cnt:
                                vv |= values[cnt] & 0xff
                            cnt += 1
                    v1 += [vv & im]

                r = 0
                for v in v1:
                    r = (r << self.state.vliwinstbits) | v
                r = r & pm

                if self.state.vliwtemplatebits < 0:
                    # Negative width: template occupies the packet's high bits.
                    res = r | (templ << (vbits - abs(self.state.vliwtemplatebits)))
                else:
                    # Positive width: template occupies the low bits.
                    res = (r << self.state.vliwtemplatebits) | templ

                q = 0
                if vbits < 8:
                    self.binary_writer.outbin(self.state.pc, res & ((1 << vbits) - 1))
                    q = 1
                elif self.state.endian == 'little':
                    total_bytes = (vbits + 7) // 8
                    for cnt in range(total_bytes):
                        self.binary_writer.outbin(self.state.pc + cnt, res & 0xff)
                        res >>= 8
                        q += 1
                else:
                    total_bytes = (vbits + 7) // 8
                    for cnt in range(total_bytes):
                        shift = (total_bytes - 1 - cnt) * 8
                        self.binary_writer.outbin(self.state.pc + cnt, (res >> shift) & 0xff)
                        q += 1

                self.state.pc += q
                break
        else:
            if self.state.should_report_errors():
                print(" error - No vliw instruction-set defined.", file=sys.stderr)
            return False
        return True


class AssemblyDirectiveProcessor:
    """Handles source-file (`.asm`-side) directives: label definitions
    (including `.EQU`), `.SECTION`/`.ENDSECTION`, `.ALIGN`, `.ORG`,
    `.ASCII`/`.ASCIZ`, `.RESB`/`.ZERO`, `.EXTERN`, `.EXPORT`/`.GLOBAL`.

    `section_processing`/`endsection_processing`/`align_processing` are the
    methods most directly responsible for maintaining `state.section_ranges`
    (the chronological list of section fragments) and for converting the
    monotonic global `state.pc` to a section-relative position wherever the
    *output file's* byte layout — not raw assembly order — is what matters;
    see `LabelManager._section_relative_offset` for the full rationale.
    """

    def __init__(self, state, expr_eval, binary_writer, label_manager, parser):
        self.state = state
        self.expr_eval = expr_eval
        self.binary_writer = binary_writer
        self.label_manager = label_manager
        self.parser = parser

    def labelc_processing(self, l, ll):
        """`.LABELC extrachars` — extend the character set allowed in label words."""
        if l.upper() != '.LABELC':
            return False
        if ll:
            self.state.lwordchars = ALPHABET + DIGIT + ll
        return True

    def label_processing(self, l):
        """Recognize and consume a leading `label:` (or `label: .EQU expr[::reloctype]`)
        on source line `l`, defining the label at the current pc (or at the
        `.EQU` expression's value) and returning the remainder of the line
        for further directive/instruction processing. Returns `l` unchanged
        if there's no label here, or "" if the whole line was consumed by
        `.EQU` (which has no further content) or the label definition failed."""
        if l == "":
            return ""

        label, idx = self.parser.get_label_word(l, 0)
        lidx = idx

        if label != "" and idx > 0 and l[idx - 1] == ':':
            idx = StringUtils.skipspc(l, idx)
            e, idx = StringUtils.get_param_to_spc(l, idx)

            if e.upper() == '.EQU':
                reloc_type = None
                # An explicit `::reloctype` suffix (e.g. `tape_a: .equ tape::abs32`)
                # marks this label as an ELF-relocation-generating alias: its value
                # must stay the label's raw (non-section-relative) pc so the
                # relocation addend math stays consistent — see _equ_sections_touched
                # below and LabelManager.get_value's is_equ/reloc_type branches.
                expr_part = l[idx:].strip()
                if '::' in expr_part:
                    parts = [p.strip() for p in expr_part.split('::', 1)]
                    expr_part = parts[0]
                    rt_str = parts[1].lower()

                    _mach_tbl = ELF_MACHINES.get(self.state.elf_machine)
                    reloc_type = _mach_tbl['named'].get(rt_str) if _mach_tbl else None
                    if reloc_type is None:
                        print(f" warning - unknown reloctype '{rt_str}' in .EQU"
                              f" for machine {self.state.elf_machine}", file=sys.stderr)

                self.state.error_undefined_label = False
                saved_mode = self.state._pass1_size_mode
                if self.state.pas == 1:
                    self.state._pass1_size_mode = True

                # Only a reloc_type-LESS .EQU (no `::reloctype`) gets its referenced
                # labels' values converted to section-relative offsets (see
                # LabelManager.get_value); _equ_sections_touched, populated during
                # that evaluation, records which sections were actually referenced
                # so we can warn if the constant silently assumed a specific
                # section layout (e.g. combined labels from two sections).
                _track_sections = reloc_type is None
                if _track_sections:
                    self.state._equ_sections_touched = set()
                try:
                    u, _ = self.expr_eval.expression_asm(expr_part, 0)
                finally:
                    self.state._pass1_size_mode = saved_mode
                    _touched = self.state._equ_sections_touched
                    self.state._equ_sections_touched = None
                if (_track_sections and _touched and len(_touched) > 1
                        and self.state.should_report_errors()):
                    print(f" warning - .EQU '{label}': expression combines labels from "
                          f"multiple sections ({', '.join(sorted(_touched))}) without an "
                          f"explicit ::reloctype; the resulting constant assumes a specific "
                          f"section layout and will NOT be relocated by the linker.",
                          file=sys.stderr)
                # Bugfix: an undefined label referenced by this .EQU's
                # expression used to go completely unnoticed here -- no
                # print, no had_error -- silently baking the UNDEF sentinel
                # (or 0, during pass1's size-probe mode) into `label`'s
                # value as if it were a legitimate constant. Mirrors the
                # same check every other directive that evaluates an
                # expression already performs (.ORG/.RESB/.ZERO).
                if self.state.error_undefined_label and self.state.should_report_errors():
                    print(f" error - .EQU '{label}': expression contains undefined label.",
                          file=sys.stderr)
                    self.state.had_error = True
                ok = self.label_manager.put_value(label, u, self.state.current_section, is_equ=True, reloc_type=reloc_type)
                return ""
            else:
                ok = self.label_manager.put_value(label, self.state.pc, self.state.current_section, is_equ=False)
                if ok is False:
                    return ""
                return l[lidx:]
        return l

    def asciistr(self, l2):
        """Emit a quoted string literal's bytes one at a time via `binary_writer.outbin`
        (advancing `state.pc`), decoding `\\0`/`\\t`/`\\n`/`\\r`/`\\\\`/`\\"` and
        `\\xHH`/`\\uHHHH`/`\\UHHHHHHHH` escapes. Shared by `.ASCII` (no terminator)
        and `.ASCIZ` (caller appends a trailing NUL). Returns False if `l2`
        doesn't start with a `"`."""
        idx = 0
        if l2 == '' or l2[idx] != '"':
            return False
        idx += 1

        _word_mask = (1 << self.state.bts) - 1 if self.state.bts > 0 else 0xFF
        _truncated = False

        while idx < len(l2) and not l2[idx] == '"':
            ch = None
            if l2[idx:idx + 2] == '\\0':
                idx += 2
                ch = chr(0)
            elif l2[idx:idx + 2] == '\\t':
                idx += 2
                ch = '\t'
            elif l2[idx:idx + 2] == '\\n':
                idx += 2
                ch = '\n'
            elif l2[idx:idx + 2] == '\\r':
                idx += 2
                ch = '\r'
            elif l2[idx:idx + 2] == '\\\\':
                idx += 2
                ch = '\\'
            elif l2[idx:idx + 2] == '\\"':
                idx += 2
                ch = '"'
            elif l2[idx:idx + 2] in ('\\x', '\\X'):
                idx += 2
                hex_str = ''
                while idx < len(l2) and l2[idx] in '0123456789abcdefABCDEF' and len(hex_str) < 2:
                    hex_str += l2[idx]
                    idx += 1
                if hex_str:
                    ch = chr(int(hex_str, 16))
                else:
                    print(f" error - '\\x' escape requires at least one hex digit in string: {l2!r}", file=sys.stderr)
                    return False
            elif l2[idx:idx + 2] in ('\\u', '\\U'):
                _ndigits = 4 if l2[idx:idx + 2] == '\\u' else 8
                idx += 2
                hex_str = ''
                while idx < len(l2) and l2[idx] in '0123456789abcdefABCDEF' and len(hex_str) < _ndigits:
                    hex_str += l2[idx]
                    idx += 1
                if len(hex_str) == _ndigits:
                    try:
                        ch = chr(int(hex_str, 16))
                    except (ValueError, OverflowError):
                        print(f" error - invalid \\u/\\U escape in string: {l2!r}", file=sys.stderr)
                        return False
                else:
                    print(f" error - '\\{'u' if _ndigits == 4 else 'U'}' escape requires "
                          f"{_ndigits} hex digits in string: {l2!r}", file=sys.stderr)
                    return False
            else:
                ch = l2[idx]
                idx += 1
            if ch is not None:
                if ord(ch) > _word_mask:
                    _truncated = True
                self.binary_writer.outbin(self.state.pc, ord(ch))
                self.state.pc += 1
        if idx >= len(l2):
            print(f" warning - unterminated string literal in .ASCII/.ASCIZ: {l2!r}", file=sys.stderr)
        if _truncated and self.state.should_report_errors():
            print(f" warning - .ASCII/.ASCIZ: one or more characters exceed the output word "
                  f"width ({self.state.bts} bit(s)) and were truncated (high bits discarded): "
                  f"{l2!r}", file=sys.stderr)
        return True

    def export_processing(self, l1, l2):
        """`.EXPORT`/`.GLOBAL label, ...` — mark labels for inclusion in the
        output ELF symbol table (`state.export_labels`), snapshotting each
        one's current value/section/is-equ status. Only meaningful when error
        reporting is active (i.e. the final pass), since label values aren't
        final until then."""
        if not (self.state.should_report_errors()):
            return False
        _l1u = StringUtils.upper(l1)
        if _l1u != ".EXPORT" and _l1u != ".GLOBAL":
            return False

        idx = 0
        l2 += chr(0)
        while idx < len(l2) and l2[idx] != chr(0):
            idx = StringUtils.skipspc(l2, idx)
            s, idx = self.parser.get_label_word(l2, idx)
            if s == "":
                break
            if idx < len(l2) and l2[idx] == ':':
                idx += 1
            v = self.label_manager.get_value(s)
            sec = self.label_manager.get_section(s)
            _lentry = self.state.labels.get(s, [])
            is_equ = len(_lentry) > 2 and _lentry[2]
            self.state.export_labels[s] = [v, sec, is_equ]
            if idx < len(l2) and l2[idx] == ',':
                idx += 1
        return True

    def resb_processing(self, l1, l2):
        """`.RESB count` — reserve `count` bytes without writing them (e.g. for
        `.bss`); just advances `state.pc`, capped at `_RESB_MAX` to catch a
        runaway/misparsed count."""
        if StringUtils.upper(l1) != '.RESB':
            return False
        # get_value() no longer clears this on a successful lookup (see its
        # Bugfix comment), so callers that want a fresh per-evaluation
        # check must reset it themselves right before evaluating.
        self.state.error_undefined_label = False
        x, idx = self.expr_eval.expression_asm(l2, 0)
        if self.state.error_undefined_label:
            if self.state.should_report_errors():
                print(" error - .RESB argument contains undefined label.", file=sys.stderr)
                self.state.had_error = True
            return True
        try:
            x = int(x)
        except (OverflowError, ValueError):
            if self.state.should_report_errors():
                print(" error - .RESB argument is non-finite or invalid.", file=sys.stderr)
                self.state.had_error = True
            return True
        if x < 0:
            if self.state.should_report_errors():
                print(f" error - .RESB requires a non-negative count, got {x}.", file=sys.stderr)
                self.state.had_error = True
            return True
        _RESB_MAX = 1 << 28
        if x > _RESB_MAX:
            if self.state.should_report_errors():
                print(f" error - .RESB count {x} exceeds maximum {_RESB_MAX}.", file=sys.stderr)
                self.state.had_error = True
            return True
        self.state.pc += x
        return True

    def zero_processing(self, l1, l2):
        """`.ZERO count` — like `.RESB` but actually writes `count` zero bytes
        to the output (rather than just skipping pc), capped at `_ZERO_MAX`."""
        if StringUtils.upper(l1) != ".ZERO":
            return False
        # See resb_processing()'s comment: get_value() no longer resets
        # this for us, so reset before evaluating for a fresh check.
        self.state.error_undefined_label = False
        x, idx = self.expr_eval.expression_asm(l2, 0)
        if self.state.error_undefined_label:
            if self.state.should_report_errors():
                print(" error - .ZERO argument contains undefined label.", file=sys.stderr)
                self.state.had_error = True
            return True
        try:
            x = int(x)
        except (OverflowError, ValueError):
            if self.state.should_report_errors():
                print(" error - .ZERO argument is non-finite or invalid.", file=sys.stderr)
                self.state.had_error = True
            return True
        if x < 0:
            if self.state.should_report_errors():
                print(f" error - .ZERO requires a non-negative count, got {x}.", file=sys.stderr)
                self.state.had_error = True
            return True
        _ZERO_MAX = 1 << 28
        if x > _ZERO_MAX:
            if self.state.should_report_errors():
                print(f" error - .ZERO count {x} exceeds maximum {_ZERO_MAX}.", file=sys.stderr)
                self.state.had_error = True
            return True
        for i in range(x):
            self.binary_writer.outbin2(self.state.pc, 0x00)
            self.state.pc += 1
        return True

    def ascii_processing(self, l1, l2):
        """`.ASCII "text"` — emit the string's bytes with no terminator."""
        if StringUtils.upper(l1) != ".ASCII":
            return False
        return self.asciistr(l2)

    def asciiz_processing(self, l1, l2):
        """`.ASCIZ "text"` — like `.ASCII` but appends a trailing NUL byte."""
        if StringUtils.upper(l1) != ".ASCIZ":
            return False
        if not self.asciistr(l2):
            if self.state.should_report_errors():
                print(" error - .ASCIZ requires a quoted string.", file=sys.stderr)
                self.state.had_error = True
            return False
        self.binary_writer.outbin(self.state.pc, 0x00)
        self.state.pc += 1
        return True

    def section_processing(self, l1, l2):
        """`.SECTION`/`.SEGMENT name` — switch the current output section.
        Before switching, closes out the fragment of `old_sec` we were just
        writing: computes its length from `state.pc` minus the fragment's
        starting pc (`entry_pc`, recorded in `state.sections[old_sec][2]` the
        last time this section was entered) and appends `(old_sec, entry_pc,
        length)` to `state.section_ranges` — the record `_section_relative_offset`
        walks to translate a raw pc into its position in the final concatenated
        output. This is naturally a no-op (tentative == 0) if the section was
        already closed by a matching `.ENDSECTION`, which advances `entry_pc`
        to the current pc as it records the fragment -- but if more code ran
        in this section *after* that `.ENDSECTION` (with no intervening
        `.SECTION`), `entry_pc` is still behind `pc` and that trailing
        fragment is correctly flushed here too, rather than being dropped.
        `state.sections[name] = [start_pc, cumulative_size, entry_pc, confirmed]`
        tracks each section's first-seen start, total bytes across all its
        fragments, and this fragment's start; re-entering a section takes the
        min of the existing start and the current pc as the (possibly still
        provisional) overall start."""
        if StringUtils.upper(l1) != ".SECTION" and StringUtils.upper(l1) != ".SEGMENT":
            return False

        if l2 != '':
            old_sec = self.state.current_section
            if old_sec not in self.state.sections:
                self.state.sections[old_sec] = [0, 0, 0, False]
            old_entry = self.state.sections[old_sec]
            _entry_pc = old_entry[2] if len(old_entry) > 2 else old_entry[0]
            tentative = self.state.pc - _entry_pc
            if tentative > 0:
                old_entry[1] += tentative
                self.state.section_ranges.append((old_sec, _entry_pc, tentative))

            self.state.current_section = l2
            if l2 not in self.state.sections:
                self.state.sections[l2] = [self.state.pc, 0, self.state.pc, False]
            else:
                existing_start     = self.state.sections[l2][0]
                existing_size      = self.state.sections[l2][1]
                existing_confirmed = len(self.state.sections[l2]) > 3 and self.state.sections[l2][3]
                if existing_size == 0 and not existing_confirmed:
                    new_start = self.state.pc
                else:
                    new_start = min(existing_start, self.state.pc)

                self.state.sections[l2] = [new_start, existing_size, self.state.pc, False]
        return True

    def align_processing(self, l1, l2):
        """`.ALIGN [boundary]` — pad up to the next multiple of `boundary`
        (or the previously-set alignment if omitted). Padding must be computed
        against the SECTION-RELATIVE position, not the raw global pc: after a
        non-contiguous section re-entry (e.g. `.text` -> `.data` -> `.text`),
        the raw pc can coincidentally already sit on an alignment boundary
        while the actual output-file position is not aligned at all. We
        resolve the section-relative base via `_section_relative_offset`
        (falling back to raw pc if unresolvable), compute the padding delta
        against THAT, then apply the same delta to the raw pc — never replace
        pc outright, since raw pc must stay consistent with everything else
        that tracks it."""
        if StringUtils.upper(l1) != ".ALIGN":
            return False

        if l2 != '':
            # Bugfix: this directive never checked error_undefined_label at
            # all -- an undefined label as the boundary argument evaluated
            # to the UNDEF sentinel (an enormous but finite integer), which
            # then sailed past the `u_int <= 0` guard (it's huge and
            # positive) and got assigned directly to state.align, silently
            # corrupting all subsequent .ALIGN padding computations. Same
            # reset-before-evaluate-then-check pattern as .ORG/.RESB/.ZERO.
            self.state.error_undefined_label = False
            u, idx = self.expr_eval.expression_asm(l2, 0)
            if self.state.error_undefined_label:
                if self.state.should_report_errors():
                    print(" error - .ALIGN argument contains undefined label.", file=sys.stderr)
                    self.state.had_error = True
                return True
            try:
                u_int = int(u)
            except (OverflowError, ValueError):
                if self.state.should_report_errors():
                    print(" error - .ALIGN argument is non-finite or invalid.", file=sys.stderr)
                    self.state.had_error = True
                return True
            if u_int <= 0:
                if self.state.should_report_errors():
                    print(f" error - .ALIGN requires a positive value, got {u_int}.", file=sys.stderr)
                    self.state.had_error = True
                return True
            self.state.align = u_int

        _sec_rel = self.label_manager._section_relative_offset(
            self.state.current_section, self.state.pc)
        _base = _sec_rel if _sec_rel is not None else self.state.pc
        _padding = self.binary_writer.align_(_base) - _base
        self.state.pc += _padding
        return True

    def endsection_processing(self, l1, l2):
        """`.ENDSECTION`/`.ENDSEGMENT` — explicitly close out the current
        section's fragment (see `section_processing`'s docstring for the
        `section_ranges` mechanics) and advance this section's `entry_pc` to
        the current pc, so a later plain `.SECTION` re-entry into the same
        name computes an empty (zero-length) delta instead of re-flushing
        this same fragment. Also marks `confirmed=True`, consulted only by
        `section_processing`'s re-entry logic to pick the section's overall
        start address -- it no longer gates whether a fragment gets flushed,
        so any code that runs after `.ENDSECTION` but before the next
        `.SECTION` still has its bytes correctly recorded rather than
        silently dropped."""
        if StringUtils.upper(l1) != ".ENDSECTION" and StringUtils.upper(l1) != ".ENDSEGMENT":
            return False
        if self.state.current_section not in self.state.sections:
            print(f" error - .ENDSECTION without matching .SECTION for '{self.state.current_section}'.", file=sys.stderr)
            self.state.had_error = True
            return True
        entry = self.state.sections[self.state.current_section]
        start = entry[0]
        entry_pc = entry[2] if len(entry) > 2 else start
        block_size = self.state.pc - entry_pc
        if block_size < 0:
            print(f" warning - ENDSECTION: computed block size {block_size} < 0 for "
                  f"'{self.state.current_section}'; keeping previous size.", file=sys.stderr)
            return True
        new_size = entry[1] + block_size
        if block_size > 0:
            self.state.section_ranges.append((self.state.current_section, entry_pc, block_size))
        self.state.sections[self.state.current_section] = [start, new_size, self.state.pc, True]
        return True

    def extern_processing(self, l1, l2):
        """`.EXTERN label[::reloctype], ...` — declare an externally-defined
        symbol, choosing a machine-appropriate default relocation type (looked
        up by `state.elf_machine`) unless overridden by an explicit
        `::reloctype` suffix. Existing (already-defined, non-extern) labels
        are left alone except their reloc_type may be updated."""
        if StringUtils.upper(l1) != ".EXTERN":
            return False

        idx = 0
        l2 = l2 + chr(0)
        while idx < len(l2) and l2[idx] != chr(0):
            idx = StringUtils.skipspc(l2, idx)
            label_part, idx = self.parser.get_label_word(l2, idx)
            if not label_part:
                break

            if idx > 0 and l2[idx - 1] == ':' and idx < len(l2) and l2[idx] == ':':
                idx -= 1

            _em_ext = self.state.elf_machine
            _mach_tbl_ext = ELF_MACHINES.get(_em_ext)
            reloc_type = _mach_tbl_ext['extern_default'] if _mach_tbl_ext else 2
            if idx < len(l2) and l2[idx:idx + 2] == '::':
                idx += 2
                rt_start = idx
                while idx < len(l2) and l2[idx] not in ' \t,:' + chr(0):
                    idx += 1
                rt_str = l2[rt_start:idx].strip().lower()

                if rt_str:
                    reloc_type = _mach_tbl_ext['named'].get(rt_str) if _mach_tbl_ext else None
                    if reloc_type is None:
                        print(f" warning - unknown reloc type '{rt_str}' in .EXTERN"
                              f" for machine {_em_ext}", file=sys.stderr)

            if idx < len(l2) and l2[idx] == ':':
                idx += 1

            existing = self.state.labels.get(label_part)

            if existing is None:
                self.state.labels[label_part] = [0, '.text', False, True, reloc_type]
            elif len(existing) > 3 and existing[3]:

                if len(existing) >= 5 and reloc_type is not None:
                    existing[4] = reloc_type

            idx = StringUtils.skipspc(l2, idx)
            if idx < len(l2) and l2[idx] == ',':
                idx += 1

        return True

    def reloctype_processing(self, l1, l2):
        """`.RELOCTYPE name8,name16,name32,name64` -- from the source file,
        override the machine's default relocation type that ObjectGenerator
        picks (via ELF_MACHINES[machine]['width_guess']) for an
        auto-detected label reference of a given encoded field width, i.e.
        one with no explicit `::reloctype` suffix on its label (see
        `.EXTERN`/`.EQU ::reloctype` for that per-label form instead).

        The four comma-separated positions correspond, in order, to encoded
        field widths of 1, 2, 4, and 8 bytes. Fewer than four may be given;
        trailing positions are simply left at the machine's built-in
        default. A blank position (two consecutive commas, or a trailing
        comma) also leaves that width's mapping untouched, so a single width
        can be overridden without having to respecify the others -- e.g.
        `.reloctype pc8,pc16,pc32,abs64` sets all four, while
        `.reloctype ,,,abs64` only changes the 8-byte (64-bit) width.

        Each name must be one of the target machine's registered
        `::reloctype` names (the same set `.EXTERN`/`.EQU` accept, e.g.
        `pc8`/`pc16`/`pc32`/`pc64`/`abs8`/`abs16`/`abs32`/`abs64`/`plt32`/
        `got32`/... depending on -m/--machine) and its registered width must
        equal the position it's given in; a name that doesn't exist for this
        machine, or whose width doesn't match its position, is rejected with
        a warning and that position's previous mapping (built-in default, or
        an earlier `.reloctype` for the same width) is left in place.

        Repeated `.reloctype` directives accumulate: only the widths named
        in the *latest* directive are touched, earlier overrides for other
        widths remain active. `.reloctype` with no arguments at all is a
        no-op (equivalent to omitting the directive).

        This is a whole-file, order-independent setting (like `-m` itself,
        which selects the table `.reloctype` names are validated against) --
        it is not scoped to a `.section` or to lines following it only; the
        override applies to every subsequent auto-detected relocation for
        the rest of the assembly, in both Pass 1 and Pass 2, until changed
        by another `.reloctype`."""
        if StringUtils.upper(l1) != ".RELOCTYPE":
            return False

        _mach_tbl_rt = ELF_MACHINES.get(self.state.elf_machine)
        if _mach_tbl_rt is None:
            print(f" warning - .RELOCTYPE: no relocation table for machine "
                  f"{self.state.elf_machine}", file=sys.stderr)
            return True

        _widths = (1, 2, 4, 8)
        _parts = l2.split(',') if l2 else []
        for _i, _raw_name in enumerate(_parts):
            if _i >= len(_widths):
                print(" warning - .RELOCTYPE: too many arguments (only "
                      "4 widths -- 8/16/32/64-bit -- are supported)",
                      file=sys.stderr)
                break
            _name = _raw_name.strip().lower()
            if not _name:
                continue
            _rtype = _mach_tbl_rt['named'].get(_name)
            if _rtype is None:
                print(f" warning - unknown reloc type '{_name}' in "
                      f".RELOCTYPE for machine {self.state.elf_machine}",
                      file=sys.stderr)
                continue
            _expected_width = _widths[_i]
            _actual_width = _mach_tbl_rt['reloc_bytes'].get(_rtype)
            if _actual_width is not None and _actual_width != _expected_width:
                print(f" warning - .RELOCTYPE: '{_name}' is a "
                      f"{_actual_width * 8}-bit relocation type, but was given "
                      f"in the {_expected_width * 8}-bit position; ignored",
                      file=sys.stderr)
                continue
            self.state.reloctype_override[_expected_width] = _rtype

        return True

    def org_processing(self, l1, l2):
        """`.ORG address[,P]` — jump the pc to an absolute address. The `,P`
        suffix additionally pads the output with `state.padding` bytes to fill
        the gap (only when moving forward); without it, pc just jumps with no
        bytes written for the skipped region."""
        if StringUtils.upper(l1) != ".ORG":
            return False
        # See resb_processing()'s comment: get_value() no longer resets
        # this for us, so reset before evaluating for a fresh check.
        self.state.error_undefined_label = False
        u, idx = self.expr_eval.expression_asm(l2, 0)
        if self.state.error_undefined_label:
            if self.state.should_report_errors():
                print(" error - .ORG argument contains undefined label.", file=sys.stderr)
                self.state.had_error = True
            return True
        try:
            u = int(u)
        except (OverflowError, ValueError):
            if self.state.should_report_errors():
                print(" error - .ORG argument is non-finite or invalid.", file=sys.stderr)
                self.state.had_error = True
            return True
        if u < 0:
            if self.state.should_report_errors():
                print(f" error - .ORG address must be non-negative, got {u}.", file=sys.stderr)
                self.state.had_error = True
            return True
        if idx + 2 <= len(l2) and l2[idx:idx + 2].upper() == ',P':
            if u > self.state.pc:
                _ORG_FILL_MAX = 1 << 28
                fill_count = u - self.state.pc
                if fill_count > _ORG_FILL_MAX:
                    if self.state.should_report_errors():
                        print(f" error - .ORG ,P fill count {fill_count} exceeds maximum {_ORG_FILL_MAX}.", file=sys.stderr)
                        self.state.had_error = True
                    return True
                for i in range(fill_count):
                    self.binary_writer.outbin2(i + self.state.pc, self.state.padding)
        self.state.pc = u
        return True


class Assembler:
    """Top-level driver: owns one `AssemblerState` plus all the collaborator
    objects (parser, expression evaluator, label/symbol/variable managers,
    binary writer, directive processors, pattern matcher/reader, object
    generator, VLIW processor) and wires them together. `run()` is the
    external entry point: reads the pattern file, then runs Pass 1 (size
    relaxation, iterating until instruction sizes stop changing) and Pass 2
    (final encoding + ELF/DWARF emission) over the source file(s).
    `lineassemble2`/`lineassemble` do the actual per-source-line work of
    matching one instruction against the pattern file and emitting its
    object code; `write_elf_obj`/`_build_dwarf_sections` handle ELF64
    relocatable object file generation."""

    def __init__(self):
        self.state = AssemblerState()
        self.parser = Parser(self.state)
        self.var_manager = VariableManager(self.state)
        self.label_manager = LabelManager(self.state)
        self.symbol_manager = SymbolManager(self.state)
        self.expr_eval = ExpressionEvaluator(self.state, self.var_manager,
                                            self.label_manager, self.symbol_manager, self.parser)
        self.binary_writer = BinaryWriter(self.state)
        self.directive_proc = DirectiveProcessor(self.state, self.expr_eval, self.binary_writer,
                                                  self.symbol_manager, self.parser)
        self.pattern_matcher = PatternMatcher(self.state, self.expr_eval, self.var_manager,
                                             self.symbol_manager, self.parser)
        self.pattern_reader = PatternFileReader(self.parser)
        self.obj_gen = ObjectGenerator(self.state, self.expr_eval, self.binary_writer)
        self.vliw_proc = VLIWProcessor(self.state, self.expr_eval, self.binary_writer)
        self.asm_directive_proc = AssemblyDirectiveProcessor(self.state, self.expr_eval,
                                                             self.binary_writer, self.label_manager, self.parser)
        self._imp_sections: dict = {}

    def include_asm(self, l1, l2):
        """`.INCLUDE "file"` (source-side) — recursively assemble `file` in
        place, resolving a relative path against the including file's directory."""
        if StringUtils.upper(l1) != ".INCLUDE":
            return False
        s = StringUtils.get_string(l2)
        if s:

            if s != "stdin" and not os.path.isabs(s):
                cur = self.state.current_file
                if cur and cur not in ("(stdin)", ""):
                    base = os.path.dirname(os.path.abspath(cur))
                    s = os.path.join(base, s)
            self.fileassemble(s)
        return True

    def lineassemble2(self, line, idx):
        """Assemble one instruction starting at `line[idx:]` (used both for a
        whole non-VLIW source line and for one slot of a VLIW packet).

        First dispatches directives that can appear where an instruction is
        expected (`.SECTION`/`.ALIGN`/`.EXTERN`/etc., and pattern-file-only
        directives like `.setsym`/`.bits` encountered while scanning `state.pat`)
        by trying each `AssemblyDirectiveProcessor`/`DirectiveProcessor` method
        in turn; each returns False immediately if its keyword doesn't match,
        so this is effectively a big dispatch chain.

        If it's an ordinary instruction, tries every pattern-file entry against
        it via `pattern_matcher.match0`, using `_lead_caps` (the pattern's
        leading run of literal capital letters) as a cheap prefilter to skip
        obviously-non-matching patterns without paying for full match0's
        combinatorial optional-group expansion. Among all patterns that DO
        match, keeps the lowest-scoring one (`last_match_score` = `(n_expr,
        -n_lit, n_sym)`, so more literal text / fewer captured operands wins
        ties) via the `best` dict, snapshotting directive-affecting state
        (`_snap_dirstate`/`_restore_dirstate`) alongside each candidate so the
        chosen pattern's directive side effects (if it came from mid-file
        `.setsym` etc.) are the ones actually applied. A perfect match (no
        expression captures or literal-count tiebreak needed, i.e. score
        `(0, ..., 0)`) short-circuits the search.

        Once a winner is chosen, first does a throw-away probe encoding
        (`_pass1_size_mode=True`) purely to learn the instruction's word count
        for `state.pc_instr_end` (needed by `$.`  in later patterns before the
        real encoding runs), then does the real `makeobj()` call. On pass 1,
        an evaluation exception (e.g. a forward-referenced label not yet
        known) is tolerated via a second `_pass1_size_mode` probe purely to
        estimate size for relaxation purposes; on pass 2 the same exception is
        a real error.

        Exceptions raised by `match0` itself for individual candidate patterns
        (malformed object-code expressions, etc.) are caught and logged
        (`exc_log`) rather than aborting the whole search, so one broken
        pattern-file entry doesn't prevent trying the rest.

        Returns `(idxs, objl, ok, idx)`: `idxs` is the matched pattern's size-
        field value (row 3, `i[3]`), `objl` is the list of encoded words (empty
        if a directive consumed the line or on error), `ok` is False only on
        genuine syntax/undefined-label errors during pass 2, `idx` is the
        input position after this instruction/directive."""
        l, idx = StringUtils.get_param_to_spc(line, idx)
        l2, idx = StringUtils.get_param_to_eon(line, idx)
        l = l.rstrip()
        l2 = l2.rstrip()
        l = l.replace(' ', '')

        if self.asm_directive_proc.section_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.endsection_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.resb_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.zero_processing(l, l2):
            return 0, [], True, idx
        _l_upper = StringUtils.upper(l)
        if _l_upper == '.ASCII':
            _ok = self.asm_directive_proc.ascii_processing(l, l2)
            if not _ok and (self.state.should_report_errors()):
                print(f" error - .ASCII: failed to process string argument: {l2!r}", file=sys.stderr)
                self.state.had_error = True
            return 0, [], True, idx
        if _l_upper == '.ASCIZ':
            _ok = self.asm_directive_proc.asciiz_processing(l, l2)
            if not _ok and (self.state.should_report_errors()):
                print(f" error - .ASCIZ: failed to process string argument: {l2!r}", file=sys.stderr)
                self.state.had_error = True
            return 0, [], True, idx
        if self.include_asm(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.align_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.org_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.labelc_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.extern_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.reloctype_processing(l, l2):
            return 0, [], True, idx
        if self.asm_directive_proc.export_processing(l, l2):
            return 0, [], True, idx

        if l == "":
            return 0, [], False, idx

        se = False
        oerr = False
        pln = 0
        pl = ""
        idxs = 0
        objl = []
        loopflag = True

        best = None
        hit_sentinel = False
        first_match_exc = None

        exc_log = []

        _DIR_SCALAR_FIELDS = ('endian', 'bts', 'padding', 'swordchars',
                              'vliwbits', 'vliwinstbits', 'vliwtemplatebits',
                              'vliwflag')

        # Directives encountered while scanning the pattern file (.setsym,
        # .bits, etc., dispatched above via directive_proc) can mutate global
        # assembler state; since we try many candidate patterns before picking
        # a winner, snapshot/restore that state per-candidate so only the
        # winning pattern's directive side effects survive.
        def _snap_dirstate():
            snap = {f: getattr(self.state, f) for f in _DIR_SCALAR_FIELDS}
            snap['symbols'] = dict(self.state.symbols)
            snap['check_constraints'] = dict(self.state.check_constraints)
            snap['vliwnop'] = list(self.state.vliwnop)
            snap['vliwset'] = list(self.state.vliwset)
            return snap

        def _restore_dirstate(snap):
            for f in _DIR_SCALAR_FIELDS:
                setattr(self.state, f, snap[f])
            self.state.symbols = dict(snap['symbols'])
            self.state.check_constraints = dict(snap['check_constraints'])
            self.state.vliwnop = list(snap['vliwnop'])
            self.state.vliwset = list(snap['vliwset'])


        for i in self.state.pat:
            pln += 1
            pl = i
            self.state.vars = [VAR_UNDEF] * 26

            if i is None:
                continue
            if self.directive_proc.set_symbol(i):
                continue
            if self.directive_proc.clear_symbol(i):
                continue
            if self.directive_proc.paddingp(i):
                continue
            if self.directive_proc.bits(i):
                continue
            if self.directive_proc.symbolc(i):
                continue
            if self.directive_proc.epic(i):
                continue
            if self.directive_proc.vliwp(i):
                continue
            if self.directive_proc.check_processing(i):
                continue
            if self.directive_proc.clrcheck_processing(i):
                continue

            lw = len([_ for _ in i if _])
            if lw == 0:
                continue

            lin = (l + ' ' + l2) if l2 else l
            lin = StringUtils.reduce_spaces(lin)

            if i[0] == '':
                hit_sentinel = True
                if best is None:
                    idxs, _ = self.expr_eval.expression_pat(i[3], 0)
                break

            _pfx = _lead_caps(i[0])
            if _pfx:
                _k = 0
                _ok = True
                for _ch in lin:
                    if _ch == ' ':
                        continue
                    if _ch.upper() != _pfx[_k]:
                        _ok = False
                        break
                    _k += 1
                    if _k == len(_pfx):
                        break
                if _k < len(_pfx):
                    _ok = False
                if not _ok:
                    continue

            self.state.error_undefined_label = False

            self.state.expmode = EXP_ASM

            saved_vars = self.state.vars[:]
            saved_refs_len = len(self.state._elf_label_refs_seen)
            saved_v2l = dict(self.state._elf_var_to_label)

            try:
                self.state._in_match_attempt = True
                _match_result = self.pattern_matcher.match0(lin, i[0])
            except (ArithmeticError, KeyError, IndexError, ValueError,
                    TypeError, AttributeError, OverflowError,
                    struct.error) as _pat_exc:

                _match_result = False
                if first_match_exc is None:
                    first_match_exc = (pln, pl)
                exc_log.append((pln, pl, type(_pat_exc).__name__, str(_pat_exc)))
            finally:
                self.state._in_match_attempt = False

            if _match_result is True:
                score = self.pattern_matcher.last_match_score
                if best is None or score < best['score']:
                    best = {
                        'score': score,
                        'pln':   pln,
                        'pat':   i,
                        'vars':  self.state.vars[:],
                        'refs':  self.state._elf_label_refs_seen[saved_refs_len:],
                        'v2l':   dict(self.state._elf_var_to_label),
                        'dir':   _snap_dirstate(),
                        # Bugfix: a `!x`-captured pattern variable's value is
                        # computed once here, during this trial match (e.g.
                        # "!e" capturing "undefined_label*0 + deflab" into a
                        # plain int stored in state.vars) -- makeobj() later
                        # just reads that already-computed int back and never
                        # calls get_value() again for it. Without saving
                        # this flag here, the unconditional reset a few
                        # lines below (and again once the winning pattern is
                        # re-applied) always erased it before the final
                        # "Undefined label in expression" check downstream
                        # could ever see it, so an instruction whose only
                        # undefined-label reference was inside a `!x`
                        # capture silently encoded as if correct.
                        'error_undefined_label': self.state.error_undefined_label,
                    }

                self.state.vars = saved_vars
                del self.state._elf_label_refs_seen[saved_refs_len:]
                self.state._elf_var_to_label = saved_v2l

                if score[0] == 0 and score[2] == 0:
                    break

            self.state.error_undefined_label = False

        if best is not None and exc_log and (self.state.verbose or self.state.debug):

            _other_plns = sorted({e[0] for e in exc_log if e[0] != best['pln']})
            if _other_plns:
                print(f" warning - {len(_other_plns)} other candidate pattern(s) at line(s) "
                      f"{_other_plns} raised an exception during matching and were skipped "
                      f"in favor of pattern line {best['pln']}.  "
                      f"[{self.state.current_file}:{self.state.ln}]", file=sys.stderr)

        if best is not None:
            i = best['pat']
            pln = best['pln']
            pl = i
            loopflag = False

            _restore_dirstate(best['dir'])
            self.state.vars = best['vars'][:]
            self.state._elf_label_refs_seen.extend(best['refs'])
            self.state._elf_var_to_label = dict(best['v2l'])
            self.state.error_undefined_label = best.get('error_undefined_label', False)
            self.state.expmode = EXP_ASM

            try:
                self.state.pc_instr_start = self.state.pc
                self.state.pc_instr_end   = self.state.pc_instr_start
                # Throw-away probe encoding, purely to learn the instruction's
                # word count so pc_instr_end is available to `$.` if it's
                # referenced by this same instruction's own object-code field
                # (it needs to be set before the real makeobj() call below).
                _probe_sm_saved    = self.state._pass1_size_mode
                _probe_refs_len    = len(self.state._elf_label_refs_seen)
                _probe_widx_saved  = self.state._elf_current_word_idx
                self.state._pass1_size_mode = True
                try:
                    _probe_objl = self.obj_gen.makeobj(i[2])
                    self.state.pc_instr_end = self.state.pc_instr_start + len(_probe_objl)
                except Exception:
                    pass
                finally:
                    self.state._pass1_size_mode = _probe_sm_saved
                    del self.state._elf_label_refs_seen[_probe_refs_len:]
                    self.state._elf_current_word_idx = _probe_widx_saved
                    # Restore (not hard-reset) so the real makeobj() call
                    # just below still sees the winning pattern's captured
                    # undefined-label status (see the 'error_undefined_label'
                    # key saved on `best` above) rather than losing it here.
                    self.state.error_undefined_label = best.get('error_undefined_label', False)
                err_triggered, _err_code = self.directive_proc.error(i[1])
                if not err_triggered:
                    objl = self.obj_gen.makeobj(i[2])
                else:
                    objl = []
                idxs, _ = self.expr_eval.expression_pat(i[3], 0)
            except (ArithmeticError, KeyError, IndexError, ValueError,
                    TypeError, AttributeError, OverflowError,
                    struct.error) as _exc:
                # Pass 1 tolerates a forward-referenced label raising here (it may
                # not be defined yet); fall back to a size-only estimate so
                # relaxation can still converge. The same exception on pass 2
                # (all labels are known by then) is a genuine error (oerr=True).
                if self.state.pas == 1:
                    if self.state.debug:
                        import traceback as _tb
                        print(f" [pass1 forward-ref fallback] {type(_exc).__name__}: {_exc}", file=sys.stderr)
                        _tb.print_exc()
                    try:
                        self.state._pass1_size_mode = True
                        objl = self.obj_gen.makeobj(i[2])
                        idxs, _ = self.expr_eval.expression_pat(i[3], 0)
                    except (ArithmeticError, KeyError, IndexError, ValueError,
                            TypeError, AttributeError, OverflowError,
                            struct.error):
                        objl = []
                    finally:
                        self.state._pass1_size_mode = False
                        self.state.error_undefined_label = False
                else:
                    oerr = True
        elif hit_sentinel:
            loopflag = False
        elif first_match_exc is not None:
            pln, pl = first_match_exc
            oerr = True
            loopflag = False

        if loopflag:
            se = True
            pln = 0
            pl = ""

        if self.state.should_report_errors():
            _loc = f"  [{self.state.current_file}:{self.state.ln}]"
            if self.state.error_undefined_label:
                self.state.had_error = True
                print(f" error - Undefined label in expression.{_loc}", file=sys.stderr)
                return 0, [], False, idx
            if se:
                self.state.had_error = True
                print(f" error - Syntax error.{_loc}", file=sys.stderr)
                return 0, [], False, idx
            if oerr:
                self.state.had_error = True
                print(f" ; pat {pln} {pl} error - Illegal syntax in assemble line or pattern line.{_loc}", file=sys.stderr)
                return 0, [], False, idx

        return idxs, objl, True, idx

    def lineassemble(self, line):
        """Assemble one full source line: strip comments, apply any leading
        `label:`/`.EQU`, split VLIW slots (`!!`-separated, tracked in
        `state.vcnt`), then dispatch through `lineassemble2` to match+encode.

        For a non-VLIW instruction, this is also where ELF relocations are
        actually computed and appended to `state.relocations` (on pass 2 of a
        `-o` build): `state._elf_label_refs_seen` was populated during
        expression evaluation with `(label_name, label_raw_value, word_index)`
        for every label reference seen while encoding this instruction's
        object-code words. Consecutive same-label references are grouped into
        one relocation spanning `num_words` words (`groups`), the relocation
        type is looked up per-target-machine (`_rmap`, keyed by field byte
        width) unless the label has an explicit reloc_type override
        (`.EXTERN`/`.EQU ::reloctype`), and the addend is computed as
        `raw_val - abs_w_bytes [+ P_asm_bytes for pc-relative types]` — see
        the inline comments below for why `P_asm_bytes` must use the same
        section-relative/raw frame as `raw_val`."""
        line = line.replace('\t', ' ').replace('\n', '').replace('\r', '')
        line = StringUtils.reduce_spaces(line)
        line = StringUtils.remove_comment_asm(line)
        if line == '':
            return False

        self.state.check_constraints.clear()

        self.state.symbols = dict(self.state.patsymbols)

        line = self.asm_directive_proc.label_processing(line)

        _vparts = []
        _vpart_buf = []
        _in_dq_v = False
        _vi = 0
        while _vi < len(line):
            _vc = line[_vi]
            if _vc == '\\' and _in_dq_v:
                _vpart_buf.append(_vc)
                if _vi + 1 < len(line):
                    _vpart_buf.append(line[_vi + 1])
                _vi += 2
                continue
            if _vc == '"':
                _in_dq_v = not _in_dq_v
                _vpart_buf.append(_vc)
            elif _vc == "'" and not _in_dq_v:
                _new_vi = StringUtils.skip_squote_literal(line, _vi)
                _vpart_buf.extend(list(line[_vi:_new_vi]))
                _vi = _new_vi
                continue
            elif not _in_dq_v and line[_vi:_vi + 2] == '!!':
                _vparts.append(''.join(_vpart_buf))
                _vpart_buf = []
                _vi += 2
                continue
            else:
                _vpart_buf.append(_vc)
            _vi += 1
        _vparts.append(''.join(_vpart_buf))
        self.state.vcnt = sum(1 for _p in _vparts if _p != '')

        if self.state.elf_objfile and self.state.pas == 2:
            self.state._elf_tracking = True
            self.state._elf_label_refs_seen = []
            self.state._elf_current_word_idx = -1
            self.state._elf_var_to_label = {}
            self.state._elf_capturing_var = None

        try:
            idxs, objl, flag, idx = self.lineassemble2(line, 0)
        finally:
            self.state._elf_tracking = False

        if not flag:
            return False

        if not self.state.vliwflag or (idx >= len(line) or line[idx:idx + 2] != '!!'):
            of = len(objl)
            if self.state.elf_objfile and self.state.pas == 2 and objl and self.state._elf_label_refs_seen:
                bpw_r = max(1, (self.state.bts + 7) // 8)
                sec_name_r = self.state.current_section

                _completed_words = 0
                _entry_pc_cur = 0
                if sec_name_r in self.state.sections:
                    _sentry = self.state.sections[sec_name_r]
                    _completed_words = _sentry[1]
                    _entry_pc_cur = _sentry[2] if len(_sentry) > 2 else _sentry[0]

                valid_refs = [(ln, aw, wi) for (ln, aw, wi) in self.state._elf_label_refs_seen if wi >= 0]
                valid_refs.sort(key=lambda r: r[2])

                # Bugfix: the same label can be captured into the same output
                # word twice (e.g. two pattern variables both bound to the
                # same source operand, as in a hypothetical "DIFF L,L").
                # Left unchecked, both identical (label, word_idx) entries
                # survive the ambiguity filter just below (which only fires
                # when DIFFERENT labels collide at the same widx) and then
                # form two separate single-word groups anchored at the same
                # widx, emitting a duplicate/non-conformant .rela entry at
                # the same offset. De-duplicate exact (label, widx) repeats
                # first, keeping only the first occurrence.
                _seen_ln_wi = set()
                _deduped_refs = []
                for _r in valid_refs:
                    _key = (_r[0], _r[2])
                    if _key in _seen_ln_wi:
                        continue
                    _seen_ln_wi.add(_key)
                    _deduped_refs.append(_r)
                valid_refs = _deduped_refs

                # If two different labels were both recorded against the same
                # word index (e.g. a combined expression like `label1-label2`),
                # we can't attribute that word to a single relocation target,
                # so drop it rather than emit a wrong relocation.
                _widx_labels = {}
                for _ln, _, _wi in valid_refs:
                    _widx_labels.setdefault(_wi, set()).add(_ln)
                _ambiguous = {_wi for _wi, ns in _widx_labels.items() if len(ns) > 1}
                valid_refs = [r for r in valid_refs if r[2] not in _ambiguous]

                groups = []
                gi = 0
                while gi < len(valid_refs):
                    lname, abs_w, widx = valid_refs[gi]
                    gj = gi + 1
                    while gj < len(valid_refs) and valid_refs[gj][0] == lname and valid_refs[gj][2] == widx + (gj - gi):
                        gj += 1
                    groups.append((lname, abs_w, widx, gj - gi))
                    gi = gj

                # ELF_MACHINE_TABLE (near top of file) is the single source
                # of truth for all of this machine's relocation numbering;
                # -m/--machine is validated against it at startup, so a
                # lookup miss here can't happen for a completed run.
                _mach_tbl_la = ELF_MACHINES[self.state.elf_machine]
                # A `.reloctype` directive in the source file overrides the
                # machine's built-in per-width default on a per-width basis;
                # widths it didn't touch keep falling back to width_guess.
                _rmap = {**_mach_tbl_la['width_guess'], **self.state.reloctype_override}
                _pc_rel_types_all = _mach_tbl_la['pc_rel']

                for lname, abs_w, first_widx, num_words in groups:
                    num_bytes = num_words * bpw_r

                    rtype = 0
                    _rtype_is_default_guess = False
                    lentry = self.state.labels.get(lname)
                    _is_imported = lentry and len(lentry) > 3 and lentry[3]
                    if lentry and len(lentry) > 4 and lentry[4] is not None:
                        rtype_override = lentry[4]
                        expected = _mach_tbl_la['reloc_bytes'].get(rtype_override)
                        # Bugfix: this used to also trust the override
                        # unconditionally whenever `_is_imported` (true for
                        # every `.EXTERN` label, not just `-i`-imported
                        # ones), skipping the width check entirely. Since
                        # `.EXTERN` without an explicit `::type` always
                        # records the machine's extern_default (e.g. a
                        # 4-byte PC32-style type on x86_64) regardless of
                        # the field actually encoded, *any* narrow-field
                        # reference to a plain `.EXTERN`'d symbol (e.g. a
                        # 1-byte `Jcc rel8` to an extern label) got a
                        # relocation type wider than its field -- a linker
                        # applying it per the ELF spec overwrites whatever
                        # bytes follow. The width check must apply
                        # uniformly regardless of is_imported; only an
                        # unknown/unregistered reloc type (expected is
                        # None) still passes through unchecked.
                        if expected is None or expected == num_bytes:
                            rtype = rtype_override
                        else:
                            rtype = _rmap.get(num_bytes, 0)
                            _rtype_is_default_guess = True
                    else:
                        rtype = _rmap.get(num_bytes, 0)
                        _rtype_is_default_guess = True

                    if rtype == 0 or first_widx >= len(objl):
                        continue

                    sec_rel = (_completed_words + (self.state.pc + first_widx - _entry_pc_cur)) * bpw_r

                    word_mask = (1 << self.state.bts) - 1
                    raw_val = 0
                    if self.state.endian == 'little':
                        for k in range(num_words):
                            widx_k = first_widx + k
                            if widx_k < len(objl):
                                raw_val |= (int(objl[widx_k]) & word_mask) << (self.state.bts * k)
                    else:
                        for k in range(num_words):
                            widx_k = first_widx + k
                            if widx_k < len(objl):
                                raw_val = (raw_val << self.state.bts) | (int(objl[widx_k]) & word_mask)

                    if (isinstance(abs_w, float) and not math.isfinite(abs_w)) or \
                       _is_undef_derived(abs_w):
                        continue

                    # The embedded field value is a signed disp/offset once encoded
                    # (e.g. 0xfc in a 1-byte field means -4), so sign-extend it
                    # from the field width before using it in the addend formula
                    # below — an unsigned interpretation here would corrupt every
                    # negative displacement's addend.
                    #
                    # Bugfix: this must be the TRUE encoded bit width
                    # (num_words * state.bts), not the byte-rounded
                    # num_bytes*8. raw_val was built above using word_mask =
                    # (1<<state.bts)-1, so for a word size that isn't a
                    # multiple of 8 (e.g. .bits::11), num_bytes*8 is larger
                    # than the actual field (16 vs. 11 bits), so raw_val
                    # (which never exceeds 2**bts-1) could never reach the
                    # byte-rounded halfway point and negative values were
                    # never sign-extended -- corrupting the addend by
                    # exactly 2**bts for every negative pc-relative/relocated
                    # value on such targets.
                    _field_bits = num_words * self.state.bts
                    if _field_bits > 0 and raw_val >= (1 << (_field_bits - 1)):
                        raw_val -= (1 << _field_bits)

                    abs_w_bytes = int(abs_w) * bpw_r

                    # A field whose encoded value already equals the label's raw
                    # address (rather than a small displacement) is actually an
                    # absolute reference that only guessed a pc-relative reloc type
                    # from its byte width; reclassify to the matching abs type.
                    # Kept x86_64-only (as before consolidation): the other
                    # registered architectures' width_guess tables were built
                    # and validated without this extra reclassification step,
                    # so extending it to them would be a behavior change this
                    # pass deliberately avoids (see ELF_MACHINES' docstring).
                    if (_rtype_is_default_guess and rtype in _pc_rel_types_all
                            and raw_val == abs_w_bytes and self.state.elf_machine == 62):
                        _rmap_abs_default = {8: 1, 4: 10, 2: 12, 1: 14}
                        rtype = _rmap_abs_default.get(num_bytes, rtype)

                    if rtype in _pc_rel_types_all:
                        # addend = raw_val - abs_w_bytes + P, where P is this
                        # instruction word's own address. P MUST be expressed in
                        # the same frame (section-relative vs. raw) as raw_val's
                        # embedded `$`/`$.` computation was — otherwise addend is
                        # off by the raw/section-relative skew whenever this
                        # section isn't first in the output file. See
                        # LabelManager._section_relative_offset's docstring; this
                        # was the root cause of a real segfault (got.s/foo.c) when
                        # `.rodata` preceded `.text` and P still used raw pc while
                        # raw_val had already been converted to section-relative.
                        _P_raw = (self.state.pc + first_widx) * bpw_r
                        _P_adj = self.label_manager._section_relative_offset(
                            self.state.current_section, self.state.pc + first_widx)
                        P_asm_bytes = _P_adj * bpw_r if _P_adj is not None else _P_raw

                        addend = raw_val - abs_w_bytes + P_asm_bytes

                    else:
                        # Absolute reference: no instruction-address term needed.
                        addend = raw_val - abs_w_bytes

                    self.state.relocations.append((sec_name_r, sec_rel, lname, rtype, addend, num_bytes))

            if self.state.gen_debug and self.state.pas == 2 and of > 0:
                self.state.line_map.append(
                    (self.state.current_section, self.state.pc,
                     self.state.current_file, self.state.ln))

            for cnt in range(of):
                self.binary_writer.outbin(self.state.pc + cnt, objl[cnt])
            self.state.pc += of
        else:
            vflag = False
            try:
                vflag = self.vliw_proc.vliwprocess(line, idxs, objl, flag, idx, self.lineassemble2)
            except Exception as _vliw_exc:
                if self.state.should_report_errors():
                    print(" error - Some error(s) in vliw definition.", file=sys.stderr)

                    if self.state.verbose or self.state.debug:
                        print(f"   ({type(_vliw_exc).__name__}: {_vliw_exc})", file=sys.stderr)
            return vflag

        return True

    def lineassemble0(self, line):
        """Wrapper around `lineassemble` that additionally echoes each source
        line (with its resolved pc) when in verbose/listing mode (pass 2 with
        `-v`, or the dedicated listing pass 0) and advances `state.ln`."""
        cleaned = line.replace('\n', '').replace('\r', '')
        _show = (self.state.pas == 2 and self.state.verbose) or self.state.pas == 0
        if _show:
            self.state.cl = cleaned
            print("%016x " % self.state.pc, end='')
            print(f"{self.state.current_file} {self.state.ln} {self.state.cl} ", end='')
        f = self.lineassemble(cleaned)
        if _show:
            print("")
        self.state.ln += 1
        return f

    def setpatsymbols(self, pat):
        """Pre-scan the whole pattern file's `.setsym`/`.clearsym` directives
        once up front, building `state.patsymbols` — the symbol-table baseline
        that `lineassemble` resets `state.symbols` to before each source line
        (mid-file `.setsym`/`.clearsym` encountered during actual matching can
        still further adjust it for subsequent lines within the same pass).

        Also applies a `.bits` directive as soon as it's seen, the same way,
        so `state.bts`/`state.endian` already reflect the pattern file's real
        word width by the time `run()` processes a `-i` label-import file
        (which happens right after this call, before any source line is
        assembled) — `.bits` is normally only applied lazily while scanning
        `state.pat` during actual line assembly (see `lineassemble2`), which
        would otherwise leave `state.bts` at its default (8) during import,
        corrupting the bytes-per-word conversion `imp_label()` needs."""
        fresh = {}
        for i in pat:
            if i is None:
                continue
            if len(i) > 0 and i[0] == '.setsym':
                # Same readpat() 2-field-vs-3-field indexing quirk fixed in
                # DirectiveProcessor.set_symbol(): a name-only ".setsym::FOO"
                # line puts "FOO" in i[2], not i[1] (only the 3-field
                # ".setsym::FOO::value" form uses i[1] for the name).
                if len(i) >= 2 and i[1]:
                    key = StringUtils.upper(i[1])
                    self.state.symbols = dict(fresh)
                    v, _ = self.expr_eval.expression_pat(i[2], 0)
                    fresh[key] = v
                elif len(i) >= 3 and i[2]:
                    key = StringUtils.upper(i[2])
                    fresh[key] = 0
                continue
            if len(i) > 0 and i[0] == '.clearsym':
                if len(i) >= 3 and i[2] != '':
                    key = StringUtils.upper(i[2])
                    fresh.pop(key, None)
                else:
                    fresh = {}
                continue
            if len(i) > 0 and i[0] == '.bits':
                self.directive_proc.bits(i)
                continue
        self.state.patsymbols = fresh
        self.state.symbols = dict(fresh)

    def fileassemble(self, fn):
        """Assemble source file `fn` line by line (or `state.stdin_tmp_path`'s
        cached copy of stdin, so stdin can be read once and reused across
        both assembly passes). Tracks the include stack (`fnstack`/`lnstack`)
        for circular-`.INCLUDE` detection and for restoring `current_file`/`ln`
        on return."""

        _MAX_INCLUDE_DEPTH = 100
        if len(self.state.fnstack) >= _MAX_INCLUDE_DEPTH:
            print(f" error - .INCLUDE nesting depth exceeds {_MAX_INCLUDE_DEPTH}: '{fn}'", file=sys.stderr)
            self.state.had_error = True
            return
        try:
            abs_fn = os.path.abspath(fn) if fn not in ("stdin", "") else fn
        except Exception:
            abs_fn = fn
        for already in self.state.fnstack:
            try:
                already_abs = os.path.abspath(already) if already not in ("stdin", "", "(stdin)") else already
            except Exception:
                already_abs = already
            if abs_fn == already_abs:
                print(f" error - circular .INCLUDE detected: '{fn}' is already being assembled.", file=sys.stderr)
                self.state.had_error = True
                return

        # Bugfix: push `fn` itself (the file about to be entered), not the
        # caller's current_file. fnstack must contain the exact stack of
        # files currently open so the cycle check above can see a file that
        # re-includes ITSELF directly (`.INCLUDE` of its own name): pushing
        # the caller's file instead left `fn` absent from fnstack for its
        # first (direct) re-entry, so a self-including file got assembled
        # twice -- duplicating its emitted bytes at wrong addresses -- before
        # the cycle was finally caught one level deeper. current_file/ln are
        # restored from locals in `finally` instead, decoupling that concern
        # from the cycle-detection stack.
        _caller_file = self.state.current_file
        self.state.fnstack.append(fn)
        self.state.lnstack.append(self.state.ln)
        self.state.current_file = fn
        self.state.ln = 1

        try:
            if fn == "stdin":
                if self.state.stdin_tmp_path is None:
                    fd, tmp_path = tempfile.mkstemp(prefix="axx_", suffix=".tmp", text=True)
                    os.close(fd)
                    self.state.stdin_tmp_path = tmp_path
                    af = self.file_input_from_stdin()
                    with open(self.state.stdin_tmp_path, "wt", encoding="utf-8") as stdintmp:
                        stdintmp.write(af)
                fn = self.state.stdin_tmp_path

            with open(fn, "rt", encoding="utf-8") as f:
                af = f.readlines()

            for i in af:
                self.lineassemble0(i)
        finally:
            self.state.fnstack.pop()
            self.state.current_file = _caller_file
            self.state.ln = self.state.lnstack.pop()

    def file_input_from_stdin(self):
        """Slurp all of stdin (used once, then cached to a temp file by
        `fileassemble` so both assembly passes can re-read the same input)."""
        af = ""
        while True:
            line = sys.stdin.readline()
            if line == '':
                break
            af += line.replace('\r', '')
        return af

    def imp_label(self, l):
        """Parse one line of a `--import` label file: either a 3-field section
        record (`name\\tstart_hex\\tsize_hex`, accumulated into `_imp_sections`
        for address-to-section lookup) or a 2-field label record
        (`name[::reloctype]\\tvalue_hex`), which is registered as an imported
        (`labels[name][3] = True`) label whose section is inferred by finding
        which previously-seen section record its address falls within."""
        l = l.rstrip('\r\n')
        if not l:
            return False

        fields = l.split('\t')

        if len(fields) >= 3:
            sname = fields[0]
            try:
                start = int(fields[1], 16)
                size  = int(fields[2], 16)
            except ValueError:
                return False

            self._imp_sections.setdefault(sname, []).append((start, size))
            return True

        if len(fields) == 2:
            label = fields[0]
            if not label:
                return False

            reloc_type = None
            if '::' in label:
                label, rt_str = label.split('::', 1)
                _mach_tbl_imp = ELF_MACHINES.get(self.state.elf_machine)
                reloc_type = _mach_tbl_imp['named'].get(rt_str.lower()) if _mach_tbl_imp else None
                if reloc_type is None:
                    print(f" warning - unknown reloc type '{rt_str}' for imported label '{label}'",
                          file=sys.stderr)
            if not label:
                return False
            try:
                v = int(fields[1], 16)
            except ValueError:
                return False
            section = '.text'

            _found = False
            for sname, _ranges in self._imp_sections.items():
                for (start, size) in _ranges:
                    if size > 0 and start <= v < start + size:
                        section = sname
                        _found = True
                        break
                    if size == 0 and v == start:
                        section = sname
                        _found = True
                        break
                if _found:
                    break

            # Bugfix: `_write_export()` (see `_write_export`'s `lbl_addr`
            # computation) writes non-.EQU label addresses in BYTES
            # (word_value * bpw), matching the ELF st_value convention. But
            # `state.labels[k][0]` is used everywhere else in this file
            # (ELF st_value, DWARF addresses, $$/$. pc-relative math, ...)
            # as a raw WORD pc, which those consumers themselves multiply by
            # bpw as needed. Storing the byte-scaled `v` here directly,
            # unconverted, double-counted bpw for every reference to an
            # imported label whenever bpw != 1 (state.bts not a multiple of
            # 8) -- e.g. a label imported at byte offset 4 on a 16-bit-word
            # target (bpw=2) was silently treated as word offset 4 (byte 8)
            # instead of the correct word offset 2. Section-membership
            # comparisons above intentionally still use the byte-scaled `v`
            # against `_imp_sections`' byte-scaled ranges (both exported by
            # the same `_write_export()`, so they're mutually consistent);
            # only the value finally stored needs converting back to words.
            bpw = max(1, (self.state.bts + 7) // 8)
            v_words = v // bpw

            entry = [v_words, section, False, True]
            if reloc_type is not None:
                entry.append(reloc_type)
            self.state.labels[label] = entry
            return True

        return False

    def printaddr(self, pc):
        """Print a 16-hex-digit address prefix (verbose/listing mode)."""
        print("%016x: " % pc, end='')

    def _section_word_ranges(self, name):
        """All recorded fragments (start, length) of section `name`, in the
        order they were closed in `state.section_ranges`; falls back to the
        section's single still-open span (`state.sections[name]`) if it was
        never fragmented/closed — used by `_addr_to_word_offset` for DWARF
        line-table generation (a separate consumer of the same raw-pc-to-
        section-relative-offset problem `LabelManager._section_relative_offset`
        solves for label values)."""
        ranges = [(rs, rl) for (rn, rs, rl) in self.state.section_ranges if rn == name]
        if ranges:
            return ranges
        entry = self.state.sections.get(name)
        if entry and entry[1] > 0:
            return [(entry[0], entry[1])]
        return []

    def _addr_to_word_offset(self, name, word_pc):
        """Convert a raw global word-pc within section `name` to its word
        offset in the final concatenated section, by walking `_section_word_ranges`
        and accumulating prior fragments' lengths. Returns None if `word_pc`
        doesn't fall in any recorded fragment of this section.

        If `.SECTION`/`.SEGMENT` was never used at all this run, `state.sections`
        stays empty and no fragments were ever recorded -- write_elf_obj's own
        `not self.state.sections` branch treats that case as one single implicit
        section starting at word 0, so the raw word_pc already IS the correct
        section-relative offset; mirror that here instead of returning None
        (which previously made every DWARF address collapse to 0)."""
        if not self.state.sections:
            return word_pc
        cum = 0
        for rs, rl in self._section_word_ranges(name):
            if rs <= word_pc <= rs + rl:
                return cum + (word_pc - rs)
            cum += rl
        return None

    def _build_dwarf_sections(self, csecs, sec_name_to_idx, bpw, machine):
        """Build minimal DWARF `.debug_line`/`.debug_line_str` (DWARF5) section
        contents plus their relocations from `state.line_map` (recorded per
        emitted instruction when `--debug`/`gen_debug` is on): one line-number
        program per source file, mapping addresses back to (file, line).
        Returns `([] , [])` if debug info wasn't requested or nothing was
        recorded. `csecs`/`sec_name_to_idx` let this look up each referenced
        code section's ELF section index for the address relocations it emits."""
        line_map = self.state.line_map
        if not self.state.gen_debug or not line_map:
            return [], []

        _mach_tbl_dw = ELF_MACHINES.get(machine)
        if _mach_tbl_dw is None or _mach_tbl_dw['elfclass'] != 2:
            # This DWARF builder hardcodes 8-byte (DW_FORM_addr) addresses
            # throughout (compile-unit low_pc/high_pc, label DIEs, the line
            # program's extended-opcode address op), which is only correct
            # for a 64-bit target. Emitting it for a 32-bit machine would
            # produce structurally-wrong-width DWARF instead of just
            # incomplete DWARF, so refuse rather than silently corrupt it.
            print(f" warning - DWARF debug info (-g) is not yet supported for "
                  f"32-bit targets (machine {machine}); skipping debug sections.",
                  file=sys.stderr)
            return [], []

        import struct as _struct
        _pk = '<' if self.state.endian != 'big' else '>'

        abs64 = _mach_tbl_dw['dwarf_abs']

        def _uleb(v):
            """DWARF unsigned LEB128 encoding."""
            out = bytearray()
            v = int(v)
            while True:
                b = v & 0x7f
                v >>= 7
                if v:
                    out.append(b | 0x80)
                else:
                    out.append(b)
                    return bytes(out)

        def _sleb(v):
            """DWARF signed LEB128 encoding."""
            out = bytearray()
            v = int(v)
            while True:
                b = v & 0x7f
                v >>= 7
                if (v == 0 and not (b & 0x40)) or (v == -1 and (b & 0x40)):
                    out.append(b)
                    return bytes(out)
                out.append(b | 0x80)

        _csec_idx_by_name = {s.name: i + 1 for i, s in enumerate(csecs)}

        def _addr_to_sec(byte_addr, sec_name=None):
            """Resolve a raw byte address (optionally hinted with its known
            section name) to `(1-based ELF section index, section-relative
            byte offset)`, via `_addr_to_word_offset`; used for DIE/line-table
            address relocations, which must point at final output-file
            positions, not raw assembly pcs."""
            word_pc = byte_addr // bpw if bpw else 0
            if sec_name is not None:
                _idx = _csec_idx_by_name.get(sec_name)
                if _idx is not None:
                    _woff = self._addr_to_word_offset(sec_name, word_pc)
                    if _woff is not None:
                        return _idx, _woff * bpw
            for i, s in enumerate(csecs):
                _woff = self._addr_to_word_offset(s.name, word_pc)
                if _woff is not None:
                    return i + 1, _woff * bpw
            return None, 0

        DW_TAG_compile_unit = 0x11
        DW_TAG_label        = 0x0a
        DW_CHILDREN_yes, DW_CHILDREN_no = 1, 0
        DW_AT_name, DW_AT_low_pc, DW_AT_high_pc = 0x03, 0x11, 0x12
        DW_AT_language, DW_AT_comp_dir = 0x13, 0x1b
        DW_AT_producer, DW_AT_stmt_list = 0x25, 0x10
        DW_FORM_addr, DW_FORM_data2, DW_FORM_data8 = 0x01, 0x05, 0x07
        DW_FORM_string, DW_FORM_sec_offset = 0x08, 0x17

        # .debug_abbrev: two abbreviation codes — (1) the compile-unit DIE
        # with name/producer/comp_dir/low_pc/high_pc/stmt_list, and (2) a
        # plain label DIE (name + low_pc) emitted once per non-.EQU,
        # non-imported label below.
        abbrev = bytearray()
        abbrev += _uleb(1) + _uleb(DW_TAG_compile_unit) + bytes([DW_CHILDREN_yes])
        for at, fm in ((DW_AT_producer, DW_FORM_string),
                       (DW_AT_language, DW_FORM_data2),
                       (DW_AT_name, DW_FORM_string),
                       (DW_AT_comp_dir, DW_FORM_string),
                       (DW_AT_low_pc, DW_FORM_addr),
                       (DW_AT_high_pc, DW_FORM_data8),
                       (DW_AT_stmt_list, DW_FORM_sec_offset)):
            abbrev += _uleb(at) + _uleb(fm)
        abbrev += _uleb(0) + _uleb(0)
        abbrev += _uleb(2) + _uleb(DW_TAG_label) + bytes([DW_CHILDREN_no])
        for at, fm in ((DW_AT_name, DW_FORM_string),
                       (DW_AT_low_pc, DW_FORM_addr)):
            abbrev += _uleb(at) + _uleb(fm)
        abbrev += _uleb(0) + _uleb(0)
        abbrev += _uleb(0)
        abbrev = bytes(abbrev)

        primary_sec = line_map[0][0]
        primary_idx = sec_name_to_idx.get(primary_sec)
        if primary_idx is None:
            primary_idx = 1 if csecs else None
        primary_csec = csecs[primary_idx - 1] if primary_idx else None
        primary_size = primary_csec.byte_size if primary_csec else 0

        producer = "axx general assembler (DWARF4)"
        comp_dir = os.getcwd()
        cu_name = line_map[0][2] or "(source)"

        # .debug_info: one compile_unit DIE followed by one label DIE per
        # exported/real label. info_relas collects (offset-into-die, section,
        # reloc-type, addend) tuples for the low_pc fields, which need actual
        # ELF relocations since the assembler doesn't know final link-time
        # addresses (this is a relocatable .o, not a linked executable).
        info_relas = []
        die = bytearray()
        die += _uleb(1)
        die += producer.encode() + b'\x00'
        die += _struct.pack(f'{_pk}H', 0x8001)
        die += cu_name.encode() + b'\x00'
        die += comp_dir.encode() + b'\x00'
        if primary_idx:
            info_relas.append((len(die), primary_idx, abs64, 0))
        die += b'\x00' * 8
        die += _struct.pack(f'{_pk}Q', primary_size & 0xFFFFFFFFFFFFFFFF)
        die += _struct.pack(f'{_pk}I', 0)
        for name, *_rest in sorted(self.state.labels.items()):
            entry = _rest[0]
            val = entry[0]
            is_equ = len(entry) > 2 and entry[2]
            is_imported = len(entry) > 3 and entry[3]
            if is_equ or is_imported:
                continue
            try:
                byte_addr = int(val) * bpw
            except (TypeError, ValueError, OverflowError):
                continue
            sidx, off = _addr_to_sec(byte_addr, entry[1])
            if sidx is None:
                continue
            die += _uleb(2)
            die += name.encode() + b'\x00'
            info_relas.append((len(die), sidx, abs64, off))
            die += b'\x00' * 8
        die += _uleb(0)

        info_body = (_struct.pack(f'{_pk}H', 4)
                     + _struct.pack(f'{_pk}I', 0)
                     + bytes([8])
                     + bytes(die))
        debug_info = _struct.pack(f'{_pk}I', len(info_body)) + info_body
        _info_prefix = 4 + 2 + 4 + 1
        info_relas = [(_info_prefix + o, s, t, a) for (o, s, t, a) in info_relas]

        files = []
        file_idx = {}
        for (_sec, _wpc, fn, _ln) in line_map:
            fn = fn or "(source)"
            if fn not in file_idx:
                files.append(fn)
                file_idx[fn] = len(files)

        # .debug_line: DWARF5 line-number program header (fixed opcode-base/
        # standard-opcode-lengths, one directory, one file-name entry per
        # distinct source file seen in line_map) followed by one line-number
        # program per section that had instructions, each row advancing
        # file/line/address registers by delta from the previous emitted row.
        hbody = bytearray()
        hbody += bytes([1])
        hbody += bytes([1])
        hbody += bytes([1])
        hbody += _struct.pack('b', -5)
        hbody += bytes([14])
        hbody += bytes([13])
        hbody += bytes([0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1])
        hbody += b'\x00'
        for fn in files:
            hbody += fn.encode() + b'\x00' + _uleb(0) + _uleb(0) + _uleb(0)
        hbody += b'\x00'

        from collections import defaultdict as _dd
        rows_by_sec = _dd(list)
        for (sec, wpc, fn, ln) in line_map:
            sidx = sec_name_to_idx.get(sec)
            if sidx is None:
                continue
            rows_by_sec[sidx].append((wpc, file_idx.get(fn or "(source)", 1), ln))

        line_relas = []
        prog = bytearray()
        prog_base = 4 + 2 + 4 + len(hbody)

        for sidx in sorted(rows_by_sec.keys()):
            rows = sorted(rows_by_sec[sidx], key=lambda r: r[0])
            csec = csecs[sidx - 1]

            def _woff(wpc, _name=csec.name):
                _o = self._addr_to_word_offset(_name, wpc)
                return _o if _o is not None else 0
            first_off = _woff(rows[0][0]) * bpw
            prog += b'\x00' + _uleb(1 + 8) + b'\x02'
            line_relas.append((prog_base + len(prog), sidx, abs64, first_off))
            prog += b'\x00' * 8
            cur_off = first_off
            cur_line = 1
            cur_file = 1
            for (wpc, fidx, ln) in rows:
                byte_off = _woff(wpc) * bpw
                if fidx != cur_file:
                    prog += bytes([4]) + _uleb(fidx)
                    cur_file = fidx
                if ln != cur_line:
                    prog += bytes([3]) + _sleb(ln - cur_line)
                    cur_line = ln
                if byte_off > cur_off:
                    prog += bytes([2]) + _uleb(byte_off - cur_off)
                    cur_off = byte_off
                prog += bytes([1])
            end_off = csec.byte_size
            if end_off > cur_off:
                prog += bytes([2]) + _uleb(end_off - cur_off)
            prog += b'\x00' + _uleb(1) + b'\x01'

        line_body = (_struct.pack(f'{_pk}H', 4)
                     + _struct.pack(f'{_pk}I', len(hbody))
                     + bytes(hbody)
                     + bytes(prog))
        debug_line = _struct.pack(f'{_pk}I', len(line_body)) + line_body

        def _pack_relas(entries):
            """Pack `(offset, symbol_idx, reloc_type, addend)` tuples into raw
            Elf64_Rela records, clamping the addend to signed-64 range."""
            out = bytearray()
            _S64_MAX, _S64_MIN = (1 << 63) - 1, -(1 << 63)
            for (off, sym, rtype, addend) in entries:
                r_info = (sym << 32) | (rtype & 0xffffffff)
                a = addend
                if a > _S64_MAX:
                    a = _S64_MAX
                elif a < _S64_MIN:
                    a = _S64_MIN
                out += _struct.pack(f'{_pk}QQq', off, r_info, a)
            return bytes(out)

        prog_sections = [
            ('.debug_abbrev', abbrev),
            ('.debug_info',   debug_info),
            ('.debug_line',   debug_line),
        ]
        rela_list = []
        if info_relas:
            rela_list.append(('.rela.debug_info', '.debug_info', _pack_relas(info_relas)))
        if line_relas:
            rela_list.append(('.rela.debug_line', '.debug_line', _pack_relas(line_relas)))

        return prog_sections, rela_list

    def write_elf_obj(self, path: str, machine: int = 62) -> None:
        """Emit an ELF32 or ELF64 relocatable object file (`.o`) at `path`
        (ELF class selected by `ELF_MACHINES[machine]['elfclass']`): builds
        one output section per distinct section name seen (`_CSec`,
        extracting its bytes from the sparse `binary_writer._buffer` via
        `_extract`), appends DWARF debug sections from `_build_dwarf_sections`
        if enabled (64-bit targets only -- see that method), builds the
        symbol table (locals, then exported/extern globals) and `.rela.*`
        sections for `state.relocations` plus any DWARF relocations, and
        writes the ELF header/section headers/`.shstrtab`/`.strtab`/
        `.symtab` framing around it all. No linking is done here —
        relocation addends were already computed correctly for the *final*
        object-file section layout back in `lineassemble`/
        `_build_dwarf_sections`; this method's job is purely to serialize
        sections/symbols/relocations to the on-disk ELF format.

        Emits RELA (`.rela.*`, explicit per-entry addend) or REL (`.rel.*`,
        no addend field -- the addend is instead baked directly into the
        relocated field's bytes) according to `ELF_MACHINES[machine]['is_rela']`,
        matching each target's real psABI convention (i386 and ARM(32) use
        REL; everything else in this table uses RELA). For a REL target,
        the byte-patching pass right after `rela_entries` is built below
        overwrites each relocated field with the addend value, since
        nothing else would otherwise record it once the .o is written."""
        import struct as _struct

        bpw = max(1, (self.state.bts + 7) // 8)
        buf = self.binary_writer._buffer

        _is_le    = (self.state.endian != 'big')
        _ei_data  = 1 if _is_le else 2
        _pk       = '<' if _is_le else '>'

        _elfclass  = ELF_MACHINES.get(machine, {}).get('elfclass', 2)
        _is_elf64  = (_elfclass == 2)
        _ehdr_size = 64 if _is_elf64 else 52
        _word_mask = 0xFFFFFFFFFFFFFFFF if _is_elf64 else 0xFFFFFFFF

        def _pack_ehdr(e_type, e_machine, e_shoff, e_shnum, e_shstrndx):
            """Pack the Elf64_Ehdr/Elf32_Ehdr (section-header-only layout: no
            program headers, entry point 0 — this is a relocatable object)."""
            ident = (b'\x7fELF'
                     + bytes([2 if _is_elf64 else 1, _ei_data, 1, self.state.osabi])
                     + b'\x00' * 8)
            if _is_elf64:
                return ident + _struct.pack(f'{_pk}HHIQQQIHHHHHH',
                    e_type, e_machine,
                    1,
                    0,
                    0,
                    e_shoff,
                    0,
                    _ehdr_size,
                    0, 0,
                    64,
                    e_shnum,
                    e_shstrndx)
            else:
                return ident + _struct.pack(f'{_pk}HHIIIIIHHHHHH',
                    e_type, e_machine,
                    1,
                    0,
                    0,
                    e_shoff,
                    0,
                    _ehdr_size,
                    0, 0,
                    40,
                    e_shnum,
                    e_shstrndx)

        def _pack_shdr(sh_name, sh_type, sh_flags, sh_addr, sh_offset,
                       sh_size, sh_link, sh_info, sh_addralign, sh_entsize):
            """Pack one Elf64_Shdr/Elf32_Shdr section header."""
            if _is_elf64:
                return _struct.pack(f'{_pk}IIQQQQIIQQ',
                    sh_name, sh_type, sh_flags, sh_addr, sh_offset,
                    sh_size, sh_link, sh_info, sh_addralign, sh_entsize)
            return _struct.pack(f'{_pk}IIIIIIIIII',
                sh_name, sh_type, sh_flags, sh_addr, sh_offset,
                sh_size, sh_link, sh_info, sh_addralign, sh_entsize)

        def _pack_sym(st_name, st_info, st_other, st_shndx, st_value, st_size):
            """Pack one Elf64_Sym/Elf32_Sym symbol table entry. Field ORDER
            (not just field width) differs between the two: Elf64_Sym is
            name/info/other/shndx/value/size, but Elf32_Sym is
            name/value/size/info/other/shndx."""
            if _is_elf64:
                return _struct.pack(f'{_pk}IBBHQQ',
                    st_name, st_info, st_other, st_shndx, st_value, st_size)
            return _struct.pack(f'{_pk}IIIBBH',
                st_name, st_value, st_size, st_info, st_other, st_shndx)

        def _align_up(x, a):
            return (x + a - 1) & ~(a - 1)

        def _extract(w_start, w_count):
            """Extract `w_count` words starting at global word-pc `w_start`
            from the sparse `binary_writer._buffer` dict, filling any unwritten
            word with `state.padding` (so gaps left by e.g. `.ORG` without
            `,P`, or by relaxation shrinking an earlier instruction, still
            produce well-defined output bytes)."""
            n = w_count * bpw
            if n == 0:
                return b''
            pad = int(self.state.padding) & ((1 << self.state.bts) - 1)
            if pad:
                tmp = pad
                if self.state.endian == 'little':
                    pad_bytes = bytes([(tmp >> (8 * j)) & 0xff for j in range(bpw)])
                else:
                    pad_bytes = bytes([(tmp >> (8 * (bpw - 1 - j))) & 0xff for j in range(bpw)])
                data = bytearray(pad_bytes * w_count)
            else:
                data = bytearray(n)
            for pos, val in buf.items():
                if pos < w_start or pos >= w_start + w_count:
                    continue
                off = (pos - w_start) * bpw
                tmp = val
                if self.state.endian == 'little':
                    for j in range(bpw):
                        if off + j < n:
                            data[off + j] = tmp & 0xff
                        tmp >>= 8
                else:
                    for j in range(bpw - 1, -1, -1):
                        if off + j < n:
                            data[off + j] = tmp & 0xff
                        tmp >>= 8
            return bytes(data)

        class _CSec:
            """One finished output section's name, extracted byte data, and ELF flags."""
            __slots__ = ('name', 'byte_start', 'data', 'byte_size', 'flags')

            def __init__(self, name, byte_start, data, flags):
                self.name       = name
                self.byte_start = byte_start
                self.data       = data
                self.byte_size  = len(data)
                self.flags      = flags

        # Build one output section per section name, concatenating each
        # section's fragments in the order they were closed (_section_word_ranges)
        # rather than by raw pc — this is the byte layout the linker will
        # actually see, and must match what _find_shndx/relocations assume.
        csecs = []
        max_w = max(buf.keys(), default=-1)

        if not self.state.sections:
            w_count = max_w + 1 if max_w >= 0 else 0
            csecs.append(_CSec('.text', 0, _extract(0, w_count), 0x2 | 0x4))
        else:
            sec_names = list(self.state.sections.keys())
            for i, sname in enumerate(sec_names):

                ranges = self._section_word_ranges(sname)
                w0 = ranges[0][0] if ranges else self.state.sections[sname][0]
                byte_start = w0 * bpw
                data = b''.join(_extract(rs, rl) for rs, rl in ranges)
                uname = sname.upper()
                if   uname.startswith('.TEXT'):
                    flags = 0x2 | 0x4
                elif uname.startswith('.DATA'):
                    flags = 0x2 | 0x1
                elif uname.startswith('.RODATA'):
                    flags = 0x2
                elif uname.startswith('.BSS'):
                    flags = 0x2 | 0x1
                else:
                    flags = 0x2
                csecs.append(_CSec(sname, byte_start, data, flags))

        ncs = len(csecs)

        sec_name_to_idx = {s.name: i + 1 for i, s in enumerate(csecs)}

        _mach_tbl_w = ELF_MACHINES.get(machine, {})
        _is_rela = _mach_tbl_w.get('is_rela', True)

        from collections import defaultdict as _defaultdict
        rela_entries = _defaultdict(list)
        for (sname, off, sym_name, rtype, addend, nbytes) in self.state.relocations:
            sidx = sec_name_to_idx.get(sname, 0)
            if sidx:
                rela_entries[sidx].append((off, sym_name, rtype, addend, nbytes))

        if not _is_rela:
            # REL-style target (see ELF_MACHINES' `is_rela` docstring): there
            # is no addend field in the relocation entry, so the addend
            # `lineassemble` computed must be baked directly into the
            # relocated field's bytes instead of the *originally encoded*
            # value (raw_val) that's there now -- a REL consumer reads that
            # field back as the implicit addend.
            for sidx, entries in rela_entries.items():
                csec = csecs[sidx - 1]
                patched = bytearray(csec.data)
                for (off, _sym_name, _rtype, addend, nbytes) in entries:
                    field = addend & ((1 << (nbytes * 8)) - 1)
                    if self.state.endian == 'little':
                        field_bytes = bytes((field >> (8 * j)) & 0xff for j in range(nbytes))
                    else:
                        field_bytes = bytes((field >> (8 * (nbytes - 1 - j))) & 0xff
                                             for j in range(nbytes))
                    if 0 <= off and off + nbytes <= len(patched):
                        patched[off:off + nbytes] = field_bytes
                csec.data = bytes(patched)

        rela_sec_order = [i + 1 for i, s in enumerate(csecs) if (i + 1) in rela_entries]
        nrela = len(rela_sec_order)

        dbg_prog, dbg_rela = self._build_dwarf_sections(
            csecs, sec_name_to_idx, bpw, machine)

        shstrtab = bytearray(b'\x00')
        sec_name_offs = []
        for s in csecs:
            sec_name_offs.append(len(shstrtab))
            shstrtab += s.name.encode() + b'\x00'
        _rela_prefix = '.rela' if _is_rela else '.rel'
        rela_name_offs = []
        for sidx in rela_sec_order:
            rela_name_offs.append(len(shstrtab))
            shstrtab += (_rela_prefix + csecs[sidx - 1].name).encode() + b'\x00'
        symtab_name_off   = len(shstrtab)
        shstrtab += b'.symtab\x00'
        strtab_name_off   = len(shstrtab)
        shstrtab += b'.strtab\x00'
        shstrtab_name_off = len(shstrtab)
        shstrtab += b'.shstrtab\x00'
        dbg_prog_name_offs = []
        for (dname, _ddata) in dbg_prog:
            dbg_prog_name_offs.append(len(shstrtab))
            shstrtab += dname.encode() + b'\x00'
        dbg_rela_name_offs = []
        for (rname, _tname, _rdata) in dbg_rela:
            dbg_rela_name_offs.append(len(shstrtab))
            shstrtab += rname.encode() + b'\x00'
        shstrtab = bytes(shstrtab)

        def _find_shndx(byte_addr, sec_name=None):
            """Resolve a raw byte address (with a section-name hint when known)
            to `(1-based section header index, section-relative byte offset)`
            for a symbol table entry. Falls back to a nearest-section guess by
            `byte_start` only if the address can't be placed in any recorded
            fragment (shouldn't normally happen for real labels)."""
            word_pc = byte_addr // bpw if bpw else 0
            if sec_name is not None:
                _idx = sec_name_to_idx.get(sec_name)
                if _idx is not None:
                    _woff = self._addr_to_word_offset(sec_name, word_pc)
                    if _woff is not None:
                        return _idx, _woff * bpw
            for i, s in enumerate(csecs):
                _woff = self._addr_to_word_offset(s.name, word_pc)
                if _woff is not None:
                    return i + 1, _woff * bpw
            if csecs:
                best_i = 0
                best_start = csecs[0].byte_start
                for i, s in enumerate(csecs):
                    if s.byte_start <= byte_addr and s.byte_start >= best_start:
                        best_i = i
                        best_start = s.byte_start
                sym_val = byte_addr - csecs[best_i].byte_start
                if sym_val < 0:
                    sym_val = 0
                return best_i + 1, sym_val
            return 0xfff1, byte_addr

        strtab = bytearray(b'\x00')
        syms   = []

        # ELF requires all STB_LOCAL symbols to precede STB_GLOBAL ones in
        # .symtab (st_info's binding nibble), tracked by sh_info on .symtab
        # (first_global, set below). Order here: null symbol, one STT_SECTION
        # symbol per section, then local (non-exported, non-imported) labels,
        # then imported labels, then exported labels — all as globals.
        syms.append(_pack_sym(0, 0, 0, 0, 0, 0))

        for i in range(ncs):
            syms.append(_pack_sym(0, 0x03, 0, i + 1, 0, 0))

        export_keys = set(self.state.export_labels.keys())

        for name, *_lentry in sorted(self.state.labels.items()):
            val         = _lentry[0][0]
            _lsec       = _lentry[0][1]
            is_equ      = len(_lentry[0]) > 2 and _lentry[0][2]
            is_imported = len(_lentry[0]) > 3 and _lentry[0][3]
            if name in export_keys or is_imported:
                continue
            # A plain .EQU (no ::reloctype) is a pure constant, not tied to any
            # section — encode it as SHN_ABS (0xfff1) with its raw value; one
            # WITH a reloc_type override is a section-relocatable alias (like
            # tape_a) and must resolve to a real section+offset instead.
            _equ_has_reloc = is_equ and len(_lentry[0]) > 4 and _lentry[0][4] is not None
            if is_equ and not _equ_has_reloc:
                shndx, sym_val = 0xfff1, val
            else:
                byte_addr = val * bpw
                shndx, sym_val = _find_shndx(byte_addr, _lsec)
            sym_val = int(sym_val) & _word_mask
            name_off = len(strtab)
            strtab += name.encode() + b'\x00'
            syms.append(_pack_sym(name_off, 0x00, 0, shndx, sym_val, 0))

        first_global = len(syms)

        for name, *_lentry in sorted(self.state.labels.items()):
            is_imported = len(_lentry[0]) > 3 and _lentry[0][3]
            if not is_imported or name in export_keys:
                continue
            name_off = len(strtab)
            strtab += name.encode() + b'\x00'
            syms.append(_pack_sym(name_off, 0x10, 0, 0, 0, 0))

        for name, *_eentry in sorted(self.state.export_labels.items()):
            val, _sec = _eentry[0][0], _eentry[0][1]
            if _is_undef_derived(val):
                continue
            is_equ = len(_eentry[0]) > 2 and _eentry[0][2]
            _lbl = self.state.labels.get(name, [])
            _equ_has_reloc = is_equ and len(_lbl) > 4 and _lbl[4] is not None
            if is_equ and not _equ_has_reloc:
                shndx, sym_val = 0xfff1, val
            else:
                byte_addr = val * bpw
                shndx, sym_val = _find_shndx(byte_addr, _sec)
            sym_val = int(sym_val) & _word_mask
            name_off = len(strtab)
            strtab += name.encode() + b'\x00'
            syms.append(_pack_sym(name_off, 0x10, 0, shndx, sym_val, 0))

        symtab = b''.join(syms)
        strtab = bytes(strtab)

        sym_name_to_idx = {}
        _si = 1 + ncs

        for name, *_lentry in sorted(self.state.labels.items()):
            is_imported = len(_lentry[0]) > 3 and _lentry[0][3]
            if name in export_keys or is_imported:
                continue
            sym_name_to_idx[name] = _si
            _si += 1

        for name, *_lentry in sorted(self.state.labels.items()):
            is_imported = len(_lentry[0]) > 3 and _lentry[0][3]
            if not is_imported or name in export_keys:
                continue
            sym_name_to_idx[name] = _si
            _si += 1

        for name, *_eentry in sorted(self.state.export_labels.items()):
            sym_name_to_idx[name] = _si
            _si += 1

        _RELA_ENTSIZE = 24 if _is_elf64 else 12
        _REL_ENTSIZE  = 16 if _is_elf64 else 8
        _REL_ENTSIZE_ACTIVE = _RELA_ENTSIZE if _is_rela else _REL_ENTSIZE

        def _pack_rela(r_offset, r_sym, r_type, r_addend):
            """Pack one Elf64_Rela/Elf32_Rela record (explicit addend).
            r_info's bit layout differs between the two classes -- Elf64
            packs a 32-bit sym index and a 32-bit type into 64 bits
            (`sym<<32 | type`), but Elf32 packs an only-24-bit sym index and
            an 8-bit type into 32 bits (`sym<<8 | type`); every
            relocation-type number this assembler uses for a 32-bit-class
            machine fits in 8 bits (see ELF_MACHINES), so no truncation
            happens in practice."""
            if _is_elf64:
                r_info = (r_sym << 32) | (r_type & 0xffffffff)
                _MAX, _MIN = (1 << 63) - 1, -(1 << 63)
                if r_addend > _MAX:
                    r_addend = _MAX
                elif r_addend < _MIN:
                    r_addend = _MIN
                return _struct.pack(f'{_pk}QQq', r_offset, r_info, r_addend)
            r_info = ((r_sym & 0xffffff) << 8) | (r_type & 0xff)
            _MAX, _MIN = (1 << 31) - 1, -(1 << 31)
            if r_addend > _MAX:
                r_addend = _MAX
            elif r_addend < _MIN:
                r_addend = _MIN
            return _struct.pack(f'{_pk}IIi', r_offset, r_info, r_addend)

        def _pack_rel(r_offset, r_sym, r_type):
            """Pack one Elf64_Rel/Elf32_Rel record: same r_info layout as
            _pack_rela's, but with no addend field at all -- the addend was
            already patched directly into the section's bytes above."""
            if _is_elf64:
                r_info = (r_sym << 32) | (r_type & 0xffffffff)
                return _struct.pack(f'{_pk}QQ', r_offset, r_info)
            r_info = ((r_sym & 0xffffff) << 8) | (r_type & 0xff)
            return _struct.pack(f'{_pk}II', r_offset, r_info)

        rela_datas = []
        for sidx in rela_sec_order:
            entries = rela_entries[sidx]
            if _is_rela:
                data = b''.join(
                    _pack_rela(off, sym_name_to_idx.get(sn, 0), rtype, addend)
                    for (off, sn, rtype, addend, _nbytes) in entries
                )
            else:
                data = b''.join(
                    _pack_rel(off, sym_name_to_idx.get(sn, 0), rtype)
                    for (off, sn, rtype, _addend, _nbytes) in entries
                )
            rela_datas.append(data)

        # File layout: Ehdr, then section data (16-byte aligned), rela data
        # (8-byte aligned), symtab, strtab, shstrtab, DWARF sections/relas
        # (64-bit targets only), then the section header table itself
        # (shdr_off) — a conventional ELF32/ELF64 relocatable-object layout
        # that any standard linker can read.
        offset = _ehdr_size
        sec_offsets = []
        for s in csecs:
            offset = _align_up(offset, 16)
            sec_offsets.append(offset)
            offset += s.byte_size

        rela_offsets = []
        for rd in rela_datas:
            offset = _align_up(offset, 8)
            rela_offsets.append(offset)
            offset += len(rd)

        symtab_off  = _align_up(offset, 8)
        offset = symtab_off + len(symtab)
        strtab_off  = offset
        offset += len(strtab)
        shstrtab_off = offset
        offset += len(shstrtab)

        base_idx = ncs + nrela + 3
        dbg_prog_offsets = []
        dbg_prog_shndx = {}
        for i, (dname, ddata) in enumerate(dbg_prog):
            offset = _align_up(offset, 1)
            dbg_prog_offsets.append(offset)
            dbg_prog_shndx[dname] = base_idx + 1 + i
            offset += len(ddata)
        dbg_rela_offsets = []
        for i, (rname, tname, rdata) in enumerate(dbg_rela):
            offset = _align_up(offset, 8)
            dbg_rela_offsets.append(offset)
            offset += len(rdata)

        shdr_off    = _align_up(offset, 8)

        ndbg = len(dbg_prog) + len(dbg_rela)
        total_shdrs = 1 + ncs + nrela + 3 + ndbg
        shstrndx    = ncs + nrela + 3
        symtab_shidx = ncs + nrela + 1
        strtab_shidx = ncs + nrela + 2
        symtab_link = strtab_shidx

        try:
            _elf_file = open(path, 'wb')
        except OSError as _e:
            print(f" error - cannot create ELF output file '{path}': {_e}", file=sys.stderr)
            return
        with _elf_file as f:
            f.write(_pack_ehdr(1, machine, shdr_off, total_shdrs, shstrndx))

            for i, s in enumerate(csecs):
                cur = f.tell()
                f.write(b'\x00' * (sec_offsets[i] - cur))
                f.write(s.data)

            for i, rd in enumerate(rela_datas):
                cur = f.tell()
                f.write(b'\x00' * (rela_offsets[i] - cur))
                f.write(rd)

            cur = f.tell()
            f.write(b'\x00' * (symtab_off - cur))
            f.write(symtab)

            f.write(strtab)

            f.write(shstrtab)

            for i, (dname, ddata) in enumerate(dbg_prog):
                cur = f.tell()
                f.write(b'\x00' * (dbg_prog_offsets[i] - cur))
                f.write(ddata)
            for i, (rname, tname, rdata) in enumerate(dbg_rela):
                cur = f.tell()
                f.write(b'\x00' * (dbg_rela_offsets[i] - cur))
                f.write(rdata)

            cur = f.tell()
            f.write(b'\x00' * (shdr_off - cur))

            f.write(_pack_shdr(0, 0, 0, 0, 0, 0, 0, 0, 0, 0))

            for i, s in enumerate(csecs):
                _sh_type_i = 8 if s.name.upper().startswith('.BSS') else 1
                f.write(_pack_shdr(
                    sec_name_offs[i], _sh_type_i, s.flags, 0,
                    sec_offsets[i], s.byte_size, 0, 0, 16, 0))

            _word_align = 8 if _is_elf64 else 4
            _sym_entsize = 24 if _is_elf64 else 16
            _rela_sh_type = 4 if _is_rela else 9   # SHT_RELA : SHT_REL
            for ri, sidx in enumerate(rela_sec_order):
                f.write(_pack_shdr(
                    rela_name_offs[ri], _rela_sh_type, 0x40, 0,
                    rela_offsets[ri], len(rela_datas[ri]),
                    symtab_shidx, sidx, _word_align, _REL_ENTSIZE_ACTIVE))

            f.write(_pack_shdr(
                symtab_name_off, 2, 0, 0,
                symtab_off, len(symtab),
                symtab_link, first_global, _word_align, _sym_entsize))

            f.write(_pack_shdr(
                strtab_name_off, 3, 0, 0,
                strtab_off, len(strtab), 0, 0, 1, 0))

            f.write(_pack_shdr(
                shstrtab_name_off, 3, 0, 0,
                shstrtab_off, len(shstrtab), 0, 0, 1, 0))

            for i, (dname, ddata) in enumerate(dbg_prog):
                f.write(_pack_shdr(
                    dbg_prog_name_offs[i], 1, 0, 0,
                    dbg_prog_offsets[i], len(ddata), 0, 0, 1, 0))
            for i, (rname, tname, rdata) in enumerate(dbg_rela):
                f.write(_pack_shdr(
                    dbg_rela_name_offs[i], 4, 0x40, 0,
                    dbg_rela_offsets[i], len(rdata),
                    symtab_shidx, dbg_prog_shndx.get(tname, 0), 8, 24))

        _dbg_msg = f", {len(dbg_prog)} debug section(s)" if dbg_prog else ""
        _reloc_kind = "rela" if _is_rela else "rel"
        print(f"elf: wrote {path} ({ncs} section(s), {nrela} {_reloc_kind} section(s), "
              f"{len(syms)} symbol(s){_dbg_msg})",
              file=sys.stderr)

    def _build_arg_parser(self):
        """Build the `argparse` CLI: `axx.py patternfile [sourcefile] [options]`,
        with `-o` selecting ELF64 object output (vs. `-b` for raw binary),
        `-e`/`-E`/`-i` for label export/import, `-m` for target machine, and
        `-g` for DWARF debug info generation (only meaningful with `-o`)."""
        import argparse
        ap = argparse.ArgumentParser(
            prog='axx',
            description='axx general assembler programmed and designed by Taisuke Maekawa',
            formatter_class=argparse.RawDescriptionHelpFormatter,
        )
        ap.add_argument('patternfile',
                        help='Pattern definition file (.axx)')
        ap.add_argument('sourcefile', nargs='?', default=None,
                        help='Assembly source file (.s). Omit for interactive mode.')

        ap.add_argument('--osabi', dest='elf_osabi', type=str, default='FreeBSD',
                        help='ELF OSABI value (default: FreeBSD; FreeBSD/Linux, case-insensitive)')
        ap.add_argument('-b', dest='outfile', default='',
                        metavar='OUTFILE',
                        help='Output binary file')
        ap.add_argument('-e', dest='expfile', default='',
                        metavar='EXPORT_TSV',
                        help='Export labels to TSV file (plain format)')
        ap.add_argument('-E', dest='expfile_elf', default='',
                        metavar='EXPORT_ELF_TSV',
                        help='Export labels to TSV file (ELF section flags format)')
        ap.add_argument('-i', dest='impfile', default='',
                        metavar='IMPORT_TSV',
                        help='Import labels from TSV file')
        ap.add_argument('-o', dest='elf_objfile', default='',
                        metavar='OBJ_FILE',
                        help='Write ELF64 relocatable object file (.o)')
        ap.add_argument('-m', dest='elf_machine', type=int, default=62,
                        metavar='MACHINE',
                        help='ELF e_machine value (default 62=EM_X86_64). '
                             'Must be one of the architectures axx has '
                             'relocation-numbering support for -- see '
                             'ELF_MACHINES near the top of this file for the '
                             'full list (currently: 3=i386, 4=M68K, '
                             '20=PowerPC, 21=PowerPC64, 22=s390x, 40=ARM, '
                             '42=SuperH, 43=SPARCV9, 62=x86-64, '
                             '183=AArch64, 243=RISC-V)')
        ap.add_argument('-v', '--verbose', dest='verbose', action='store_true',
                        default=False,
                        help='Verbose: print assembly listing to stdout (default: silent)')
        ap.add_argument('-d', '--debug', dest='debug', action='store_true',
                        default=False,
                        help='Enable debug output (forward-ref fallback, relaxation log, etc.)')
        ap.add_argument('-g', '--gen-debug', dest='gen_debug', action='store_true',
                        default=False,
                        help='Generate DWARF debug information (.debug_info/.debug_abbrev/'
                             '.debug_line) in the ELF object so that gdb/lldb can do '
                             'source-level debugging. Effective only together with -o.')
        return ap

    def run(self):
        """Top-level entry point (called from `main()`). Parses CLI args, then:

        - No sourcefile: interactive REPL mode (`pas=0`), one line at a time,
          `?` prints all labels via `LabelManager.printlabels`.
        - Sourcefile given: runs Pass 1 relaxation (`pas=1`) up to `MAX_RELAX`
          times, re-assembling the WHOLE file from scratch each iteration
          (resetting pc/labels/sections/section_ranges) since variable-length
          instructions can change size as forward-referenced label addresses
          shift, which can in turn change other instructions' sizes. Converges
          when the current iteration's `(label_pc, label_section)` snapshot
          exactly matches a previously-seen snapshot AND the cycle length is 1
          (identical to the immediately preceding iteration) — a longer cycle
          means it's oscillating between distinct layouts and will never
          settle, which is reported as a hard error since output would be
          simply wrong. Then runs Pass 2 (`pas=2`) once for real encoding +
          relocation/line-map recording, and cross-checks Pass 1's final label
          addresses against Pass 2's actual addresses (`_drift`) as a sanity
          check that relaxation genuinely converged (a mismatch here would
          mean corrupted output, so it's also a hard abort).

        Finally flushes the binary writer, optionally writes the ELF object
        (`write_elf_obj`) and/or plain-binary output, and optionally writes
        `-e`/`-E` label-export TSV files (`_write_export`, with the `-E`
        variant additionally recording each section's ELF flags and each
        label's reloc_type override, for round-tripping through `-i` in a
        later separate assembly of a different file against the same
        pattern set)."""
        ap = self._build_arg_parser()

        if len(sys.argv) == 1:
            ap.print_help()
            return True

        args = ap.parse_args()

        osabitbl = {'Linux': 0, 'linux': 0, 'FreeBSD': 9, 'freebsd': 9}

        self.state.outfile      = args.outfile
        self.state.expfile      = args.expfile
        self.state.expfile_elf  = args.expfile_elf
        self.state.impfile      = args.impfile
        self.state.elf_objfile  = args.elf_objfile

        if args.elf_machine not in ELF_MACHINES:
            _known = ', '.join(f"{m} ({ELF_MACHINES[m]['name']})" for m in sorted(ELF_MACHINES))
            print(f" error - -m/--machine value {args.elf_machine} is not a supported "
                  f"ELF e_machine number. axx only knows correct relocation-type "
                  f"numbering for: {_known}. Refusing to guess/fall back to x86_64 "
                  f"numbering for an unrecognized machine, since that would silently "
                  f"mislabel every relocation in the output.",
                  file=sys.stderr)
            return False
        self.state.elf_machine  = args.elf_machine

        if args.elf_osabi not in osabitbl:
            print(f"warning: unknown --osabi value '{args.elf_osabi}'; "
                  f"valid choices are {list(osabitbl.keys())}. Using 'FreeBSD'.",
                  file=sys.stderr)
        self.state.osabi        = osabitbl.get(args.elf_osabi, 9)
        self.state.verbose      = args.verbose
        self.state.debug        = args.debug
        self.state.gen_debug    = args.gen_debug

        try:
            self.state.pat = self.pattern_reader.readpat(args.patternfile)
            self.setpatsymbols(self.state.pat)

            if self.state.impfile:

                with open(self.state.impfile, 'rt', encoding="utf-8") as label_file:
                    raw_lines = label_file.readlines()
                for l in raw_lines:
                    fields = l.rstrip('\r\n').split('\t')
                    if len(fields) >= 3:
                        self.imp_label(l)
                for l in raw_lines:
                    fields = l.rstrip('\r\n').split('\t')
                    if len(fields) == 2:
                        self.imp_label(l)

            if self.state.outfile:
                try:
                    os.remove(self.state.outfile)
                except OSError:
                    pass

            if args.sourcefile is None:
                self.state.pc = 0
                self.state.pas = 0
                self.state.ln = 1
                self.state.current_file = "(stdin)"
                while True:
                    self.printaddr(self.state.pc)
                    try:
                        line = input(">> ")
                    except EOFError:
                        break
                    line = line.strip()
                    if line == "":
                        continue
                    if line == "?":
                        self.label_manager.printlabels()
                        continue
                    self.lineassemble0(line)
            else:

                MAX_RELAX = 16
                self.state._pass1_prev_label_pcs = _RELAXATION_SENTINEL
                self.state._relax_prev_values = {}

                _seen_pcs_history = {}

                _imported_labels = dict(self.state.labels)

                _initial_vars = list(self.state.vars)

                for relax_iter in range(MAX_RELAX):
                    self.state.pc = 0
                    self.state.pas = 1
                    self.state.ln = 1
                    self.state.labels = dict(_imported_labels)
                    self.state.sections = {}
                    self.state.export_labels = {}
                    self.state.current_section = '.text'
                    self.state.symbols = dict(self.state.patsymbols)
                    self.state.vars = list(_initial_vars)
                    self.state.section_ranges = []
                    self.fileassemble(args.sourcefile)

                    _last_sec1 = self.state.current_section
                    if _last_sec1 in self.state.sections:
                        _e1 = self.state.sections[_last_sec1]
                        _ep1 = _e1[2] if len(_e1) > 2 else _e1[0]
                        _blk1 = self.state.pc - _ep1
                        if _blk1 > 0:
                            _e1[1] += _blk1
                            self.state.section_ranges.append((_last_sec1, _ep1, _blk1))

                    # A label whose value is still UNDEF-derived means some
                    # forward reference hasn't resolved yet this iteration;
                    # convergence can't be judged from PCs alone until that
                    # clears, so skip the cycle-detection check for this round.
                    current_pcs = {k: (v[0], v[1]) for k, v in self.state.labels.items()}
                    has_undef = any(
                        _is_undef_derived(pc)
                        for k, (pc, _sec) in current_pcs.items()
                        if not (len(self.state.labels[k]) > 2 and self.state.labels[k][2])
                    )

                    self.state._relax_prev_values = {
                        k: v[0] for k, v in self.state.labels.items()
                        if not _is_undef_derived(v[0])
                    }
                    if not has_undef:
                        _pcs_key = frozenset(current_pcs.items())
                        _first_seen = _seen_pcs_history.get(_pcs_key)
                        if _first_seen is not None:
                            _cycle_len = (relax_iter + 1) - _first_seen
                            if _cycle_len == 1:
                                if self.state.debug:
                                    print(f"Pass1 relaxation converged after {relax_iter + 1} iteration(s)", file=sys.stderr)
                                break
                            else:
                                print(f" error - Pass1 relaxation is oscillating with period "
                                      f"{_cycle_len} (the instruction layout at iteration "
                                      f"{relax_iter + 1} is identical to iteration {_first_seen}); "
                                      f"it will never converge by simple repetition.", file=sys.stderr)
                                print("         Aborting: no output file written.", file=sys.stderr)
                                return False
                        _seen_pcs_history[_pcs_key] = relax_iter + 1
                    self.state._pass1_prev_label_pcs = current_pcs
                else:

                    print(" error - Pass1 relaxation did not converge after {0} iterations.".format(MAX_RELAX),
                          file=sys.stderr)
                    print("         Generated code would have incorrect addresses for", file=sys.stderr)
                    print("         variable-length instructions with forward references.", file=sys.stderr)
                    print("         Aborting: no output file written.", file=sys.stderr)
                    if isinstance(self.state._pass1_prev_label_pcs, dict):
                        changed = []
                        for k in current_pcs:
                            if k in self.state._pass1_prev_label_pcs:
                                if current_pcs[k] != self.state._pass1_prev_label_pcs[k]:
                                    changed.append(k)
                        if changed:
                            print(f"         Labels still changing: {', '.join(changed[:10])}", file=sys.stderr)
                    return False

                _pass1_final_addrs = {
                    k: v[0] for k, v in self.state.labels.items()
                    if not (len(v) > 2 and v[2])
                }

                self.state.pc = 0
                self.state.pas = 2
                self.state.ln = 1
                self.state.relocations = []
                self.state.line_map = []
                self.state.sections = {}
                self.state.current_section = '.text'
                self.state.section_ranges = []
                self.fileassemble(args.sourcefile)

                _last_sec = self.state.current_section
                if _last_sec in self.state.sections:
                    _e = self.state.sections[_last_sec]
                    _entry_pc = _e[2] if len(_e) > 2 else _e[0]
                    _block = self.state.pc - _entry_pc
                    if _block > 0:
                        _e[1] += _block
                        self.state.section_ranges.append((_last_sec, _entry_pc, _block))

                # Sanity check: Pass 1's converged addresses should exactly match
                # what Pass 2 actually computes; any mismatch means relaxation
                # didn't truly converge (a bug, not a normal condition) and the
                # emitted addresses/relocations would be wrong, so treat it as fatal.
                _drift = []
                for k, p2 in ((kk, vv[0]) for kk, vv in self.state.labels.items()
                              if not (len(vv) > 2 and vv[2])):
                    p1 = _pass1_final_addrs.get(k)
                    if p1 is not None and p1 != p2 and not _is_undef_derived(p2):
                        _drift.append((k, p1, p2))
                if _drift:
                    print(" error - address mismatch between pass1 and pass2 "
                          f"({len(_drift)} label(s)); output addresses are UNRELIABLE.",
                          file=sys.stderr)
                    print("         This usually means pass1 relaxation did not fully "
                          "converge for variable-length forward references.", file=sys.stderr)
                    for k, p1, p2 in _drift[:10]:
                        try:
                            print(f"           {k}: pass1=0x{int(p1):X} pass2=0x{int(p2):X}",
                                  file=sys.stderr)
                        except (TypeError, ValueError):
                            print(f"           {k}: pass1={p1!r} pass2={p2!r}", file=sys.stderr)
                    if len(_drift) > 10:
                        print(f"           ... and {len(_drift) - 10} more.", file=sys.stderr)
                    print("         Aborting: no output file written.", file=sys.stderr)
                    return False

                if self.state.had_error:
                    print(" error - one or more errors were reported during assembly; "
                          "output would be incomplete or wrong.", file=sys.stderr)
                    print("         Aborting: no output file written.", file=sys.stderr)
                    return False

            self.binary_writer.flush()

            if self.state.elf_objfile:
                self.write_elf_obj(self.state.elf_objfile, self.state.elf_machine)

            if self.state.expfile_elf and self.state.expfile:
                print(f"warning: both -e '{self.state.expfile}' and -E '{self.state.expfile_elf}' specified; "
                      f"exporting plain format to -e and ELF format to -E separately.",
                      file=sys.stderr)

            def _write_export(path, elf):
                """Write one export TSV: a `section\\tstart\\tsize[\\tflags]` line
                per section fragment, then a `label[::reloctype]\\taddress` line
                per exported label. `elf=1` (the `-E` form) additionally emits
                ELF section flags and each label's explicit reloc_type (if any),
                so a later `-i` import of this file preserves relocation-type
                info for cross-file references; `elf=0` (`-e`) omits both."""
                h   = list(self.state.export_labels.items())
                key = list(self.state.sections.keys())
                _bpw_export = max(1, (self.state.bts + 7) // 8)
                with open(path, 'wt', encoding="utf-8") as label_file:
                    for i in key:
                        if i == '.text' and elf == 1:
                            flag = 'AX'
                        elif i == '.data' and elf == 1:
                            flag = 'WA'
                        else:
                            flag = ''

                        ranges = [(rs, rl) for (rn, rs, rl) in self.state.section_ranges if rn == i]
                        if not ranges:
                            ranges = [(self.state.sections[i][0], self.state.sections[i][1])]
                        for (w_start, w_count) in ranges:
                            try:
                                byte_start = int(w_start) * _bpw_export
                                byte_size  = int(w_count) * _bpw_export
                            except (OverflowError, ValueError, TypeError):
                                byte_start = 0
                                byte_size  = 0
                            label_file.write(
                                f"{i}\t{byte_start:#x}\t{byte_size:#x}\t{flag}\n"
                            )
                    for i in h:
                        lbl_is_equ = len(i[1]) > 2 and i[1][2]
                        lbl_addr_raw = i[1][0] if lbl_is_equ else i[1][0] * _bpw_export
                        if _is_undef_derived(i[1][0]):
                            continue
                        try:
                            lbl_addr = int(lbl_addr_raw)
                        except (OverflowError, ValueError, TypeError):
                            lbl_addr = 0

                        reloc_type_str = ''
                        if elf == 1:
                            lentry = self.state.labels.get(i[0], [])
                            if len(lentry) > 4 and lentry[4] is not None:
                                _mach_tbl_exp = ELF_MACHINES.get(self.state.elf_machine)
                                reloc_type_str = _mach_tbl_exp['reverse'].get(lentry[4], '') if _mach_tbl_exp else ''
                                if reloc_type_str:
                                    reloc_type_str = f'::{reloc_type_str}'

                        label_file.write(f"{i[0]}{reloc_type_str}\t{lbl_addr:#x}\n")

            if self.state.expfile:
                _write_export(self.state.expfile, elf=0)
            if self.state.expfile_elf:
                _write_export(self.state.expfile_elf, elf=1)

        finally:
            if self.state.stdin_tmp_path and os.path.exists(self.state.stdin_tmp_path):
                try:
                    os.remove(self.state.stdin_tmp_path)
                except OSError:
                    pass
                self.state.stdin_tmp_path = None

        return True


def main():
    """Create a fresh `Assembler` and run it; returns True on success."""
    assembler = Assembler()
    return assembler.run()


if __name__ == '__main__':
    ok = main()
    exit(0 if ok else 1)
