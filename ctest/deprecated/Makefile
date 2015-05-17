SDCCCFLAGS = --model-large  --no-c-code-in-asm


ASLINKFLAGS = --stack-after-data  --code-loc 0x0  --data-loc 0x0 --stack-after-data --xram-loc 0x6000

%.rel : %.c %.h
	sdcc $(SDCCCFLAGS) -c $<


all: program.hex program.bin

program.hex: program.c 
	sdcc $(SDCCCFLAGS) $(ASLINKFLAGS) $^
	packihx program.ihx > program.hex

program.bin: program.ihx
	makebin program.ihx > program.bin

clean:
	rm -f program.asm 
	rm -f *.hex *.ihx *.lnk *.lst *.map *.rel *.rst *.sym *.mem *.lk *.bin


