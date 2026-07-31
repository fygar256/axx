    .ORG 0
    .asciz "test"
    INC (IX)
    INC (IY)
    INC (IX+0x56)
    INC (IY+0x56)
    DEC (IX)
    DEC (IY)
    DEC (IX+0x56)
    DEC (IY+0x56)
    .ORG 0x100,P
    LD SP,HL
    LD SP,IX
    LD SP,IY
    LD (HL),0x56
    LD (IY),0x56
    LD (IY+0x50),056
    LD (IX),E
    LD (IX+0x56),E
    LD E,(IX)
    LD E,(IX+0x56)
    LD E,(IY)
    LD E,(IY+0x56)
    LD E,(HL)
    LD (HL),E
    LD A,(0x12)
    LD (0x12),A
    LD HL,(0x56)
    LD IX,(0x56)
    LD IY,(0x56)
    LD (0x56),HL
    LD (0x56),IX
    LD (0x56),IY
    LD A,(BC)
    LD A,(DE)
    LD (HL),0x56
    LD (IX),0x56
    LD (IY),0x56
    LD (IX+0x12),0x56
    LD (IY+0x12),0x56
    LD (BC),A
    LD (DE),A
    LD A,I
    LD A,R
    LD I,A
    LD R,A
    LD IX,0x56
    LD IY,0x56
    LD HL,0x56
    LD DE,0x56
    LD BC,0x56
    LD SP,0x56
    LD HL,0x56
    LD E,0x56
    LD E,B
    PUSH  BC
    PUSH IX
    PUSH IY
    POP BC
    POP IX
    POP IY
    ADD A,(HL)
    ADD A,(IX)
    ADD A,(IY)
    ADD A,(IX+0x12)
    ADD A,(IY+0x12)
    ADD A,E
    ADD A,0x56
    ADC A,(HL)
    ADC A,(IX)
    ADC A,(IY)
    ADC A,(IX+0x12)
    ADC A,(IY+0x12)
    ADC A,E
    ADC A,0x56
    SUB (HL)
    SUB (IX)
    SUB (IY)
    SUB (IX+0x12)
    SUB (IY+0x12)
    SUB E
    SUB 0x56
    SBC A,(HL)
    SBC A,(IX)
    SBC A,(IY)
    SBC A,(IX+0x12)
    SBC A,(IY+0x12)
    SBC A,E
    SBC A,0x56
    AND (HL)
    AND (IX)
    AND (IY)
    AND (IX+3)
    AND (IY+3)
    AND E
    AND 0x56
    OR (HL)
    OR (IX)
    OR (IY)
    OR (IX+0x12)
    OR (IY+0x12)
    OR E
    OR 0x56
    XOR (HL)
    XOR (IX)
    XOR (IY)
    XOR (IX+0x12)
    XOR (IY+0x12)
    XOR E
    XOR 0x56
    CP (HL)
    CP (IX)
    CP (IY)
    CP (IX+0x12)
    CP (IY+0x12)
    CP E
    CP 0x56
    INC HL
    INC IY
    INC IX
    INC BC
    INC DE
    INC SP
    DEC HL
    DEC IY
    DEC IX
    DEC BC
    DEC DE
    DEC SP
    INC (HL)
    INC (IX)
    INC (IY)
    INC (IX+0x56)
    INC (IY+0x56)
    INC E
    DEC (HL)
    DEC (IX)
    DEC (IY)
    DEC (IX+0x56)
    DEC (IY+0x56)
    DEC E
    ADD HL,de
    ADC HL,de
    SBC HL,de
    ADD IX,de
    ADD IY,de
    DAA
    CPL
    NEG
    CCF
    SCF
    NOP
    HALT
    DI
    EI
    IM 0
    IM 1
    IM 2
    EX DE,HL
    EX AF,AF'
    EXX
    EX (SP),HL
    EX (SP),IX
    EX (SP),IY
    LDI
    LDIR
    LDD
    LDDR
    CPI
    CPIR
    CPD
    CPDR
    BIT 3,E
    BIT 3,(HL)
    BIT 3,(IX)
    BIT 3,(IY)
    BIT 3,(IX+0x56)
    BIT 3,(IY)
    SET 3,E
    SET 3,(HL)
    SET 3,(IX)
    SET 3,(IY)
    SET 3,(IX+0x56)
    SET 3,(IY)
    RES 3,E
    RES 3,(HL)
    RES 3,(IX)
    RES 3,(IY)
    RES 3,(IX+0x56)
    RES 3,(IY+0x56)
    RLCA
    RLA
    RRCA
    RRA
    RLC (HL)
    RLC (IX)
    RLC (IY)
    RLC E
    RL (HL)
    RL (IX)
    RL (IY)
    RL E
    RRC (HL)
    RRC (IX)
    RRC (IY)
    RRC E
    RR (HL)
    RR (IX)
    RR (IY)
    RR E
    SLA (HL)
    SLA (IX)
    SLA (IY)
    SLA E
    SRA (HL)
    SRA (IX)
    SRA (IY)
    SRA E
    SRL (HL)
    SRL (IX)
    SRL (IY)
    SRL E
    RLD
    RRD
    JP (HL)
    JP (IX)
    JP (IY)
    JP 0x56
    JP C,0x56
    CALL C,0x56
    CALL 0x56
    RET C
    RET
    RETI
    RETN
    RST 0x08
    IN A,(1)
    IN E,(C)
    INI
    INIR
    IND
    INDR
    OUT (0x12),A
    OUT (C),E
    OUTI
    OTIR
    OUTD
    OTDR
