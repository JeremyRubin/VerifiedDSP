void main() {
    __asm
        loop:
        /* clr C */
        nop
        setb C
        ljmp loop
    __endasm;
}
