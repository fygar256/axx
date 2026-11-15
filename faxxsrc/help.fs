\ help.fs -- axx の使い方 (argparse の --help と同じ文面)

decimal

: help-text ( -- a u )
  s\" usage: axx [-h] [--osabi ELF_OSABI] [-b OUTFILE] [-e EXPORT_TSV]\n           [-E EXPORT_ELF_TSV] [-i IMPORT_TSV] [-o OBJ_FILE] [-f {32,64}]\n           [-m MACHINE] [-v] [-V] [-d] [-g] [--no-macro] [-"
  s\" P [FILE]]\n           [--elfdesc] [-p [FILE]]\n           patternfile [sourcefile]\n\naxx general assembler programmed and designed by Taisuke Maekawa\n\npositional arguments:\n  patternfile           Patt"
  s\" ern definition file (.axx)\n  sourcefile            Assembly source file (.s). Omit for interactive mode.\n\noptions:\n  -h, --help            show this help message and exit\n  --osabi ELF_OSABI     ELF"
  s\"  OSABI value (default: Linux; FreeBSD/Linux, case-\n                        insensitive)\n  -b OUTFILE            Output binary file\n  -e EXPORT_TSV         Export labels to TSV file (plain format)\n  "
  s\" -E EXPORT_ELF_TSV     Export labels to TSV file (ELF section flags format)\n  -i IMPORT_TSV         Import labels from TSV file\n  -o OBJ_FILE           Write ELF relocatable object file (.o); class s"
  s\" elected\n                        by -f (default: ELF64)\n  -f {32,64}            ELF class for -o output: 64 for ELF64/ELFCLASS64, 32\n                        for ELF32/ELFCLASS32. Default: the pattern"
  s\"  file's\n                        .elfclass, or the conventional class of the -m machine\n                        (ELF64 if that is unknown too). Independent of\n                        -m/--machine; a "
  s\" value that does not match the\n                        machine's conventional class (e.g. -m 62 -f 32, the\n                        real x32 ABI's EM_X86_64-in-ELFCLASS32 layout) is\n                  "
  s\"       honored, with a warning. -g/--gen-debug DWARF output\n                        supports both 32 and 64.\n  -m MACHINE            ELF e_machine value (default: the pattern file's\n                 "
  s\"        .elfmachine, else 62=EM_X86_64). axx carries built-in\n                        relocation numbering for 3=i386, 4=M68K, 20=PowerPC,\n                        21=PowerPC64, 22=s390x, 40=ARM, 42=S"
  s\" uperH, 43=SPARCV9,\n                        62=x86-64, 183=AArch64, 243=RISC-V. Any other number\n                        is accepted too, but then the relocation types must\n                        co"
  s\" me from the pattern file (.elftype / .elfwidth /\n                        .elfextern, manual 3.7.7); references whose type is\n                        unknown get no relocation entry rather than a gue"
  s\" ssed\n                        one.\n  -v, --verbose         Verbose: print assembly listing to stdout (default:\n                        silent)\n  -V, --text-output     Print the text built from string"
  s\" -template patterns to\n                        stdout (default: silent). Under .textmode it writes\n                        the same bytes as -b, .emit output included. With -v\n                       "
  s\"  the same text is shown inside the listing instead.\n  -d, --debug           Enable debug output (forward-ref fallback, relaxation\n                        log, etc.)\n  -g, --gen-debug       Generate "
  s\" DWARF debug information\n                        (.debug_info/.debug_abbrev/.debug_line) in the ELF\n                        object so that gdb/lldb can do source-level debugging.\n                    "
  s\"     Effective only together with -o.\n  --no-macro            Disable the macro preprocessor layer\n                        (!if/!while/!def/!return/!set and !{...}\n                        interpolati"
  s\" on), so the source is handed to the\n                        assembler exactly as written.\n  -P, --macro-expand [FILE]\n                        Macro-expand the source file and write the resulting\n   "
  s\"                      assembly to FILE (or stdout if FILE is omitted or \"-\")\n                        without assembling it. Useful for debugging macros.\n  --elfdesc             Print the effective EL"
  s\" F machine description (the\n                        built-in table of the -m machine with the pattern\n                        file's .elf* declarations laid over it) as pattern-\n                     "
  s\"    file declarations headed by .elfbuiltin::0, and exit\n                        without assembling. Pasting the output into a pattern\n                        file reproduces the same ELF output with"
  s\"  no built-in\n                        table (manual 3.7.9).\n  -p, --macro-expand-pattern [FILE]\n                        The pattern-file counterpart of -P: macro-expand the\n                        pa"
  s\" ttern file and write the resulting pattern text to\n                        FILE (or stdout if FILE is omitted or \"-\") without\n                        assembling. Useful for debugging pattern-file ma"
  s\" cros.\n"
  sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat sconcat ;
