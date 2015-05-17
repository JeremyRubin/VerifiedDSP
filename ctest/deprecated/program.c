void main() {
    __asm
        loop:
        /* clr C */
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        setb C
        ljmp loop
    __endasm;
}
