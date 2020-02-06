FILES=tester.c e_fmod.c e_remainder.c
ASM_FILES=tester.s e_fmod.s e_remainder.s

DEFINES=-D__LITTLE_ENDIAN

all:
	$(CC) $(FILES) $(DEFINES)
	$(CC) $(FILES) $(DEFINES) -o experiment.a.out
	$(CC) -S -masm=intel $(FILES) $(DEFINES)
#	$(CC) $(ASM_FILES) -o a.out2
