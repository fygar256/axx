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
    SUB A,(HL)
    SUB A,(IX)
    SUB A,(IY)
    SUB A,(IX+0x12)
    SUB A,(IY+0x12)
    SUB A,E
    SUB A,0x56
    SBC A,(HL)
    SBC A,(IX)
    SBC A,(IY)
    SBC A,(IX+0x12)
    SBC A,(IY+0x12)
    SBC A,E
    SBC A,0x56
    AND A,(HL)
    AND A,(IX)
    AND A,(IY)
    AND A,(IX+3)
    AND A,(IY+3)
    AND A,E
    AND A,0x56
    OR A,(HL)
    OR A,(IX)
    OR A,(IY)
    OR A,(IX+0x12)
    OR A,(IY+0x12)
    OR A,E
    OR A,0x56
    XOR A,(HL)
    XOR A,(IX)
    XOR A,(IY)
    XOR A,(IX+0x12)
    XOR A,(IY+0x12)
    XOR A,E
    XOR A,0x56
    CP A,(HL)
    CP A,(IX)
    CP A,(IY)
    CP A,(IX+0x12)
    CP A,(IY+0x12)
    CP A,E
    CP A,0x56
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
