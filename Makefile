.PHONY: model connect ctest extraction

all: model connect extraction ctest
	echo "Done Building"

model:
	cd Model && $(MAKE);


connect: model
	cd Connect && $(MAKE);



ctest:
	cd ctest && $(MAKE);

extraction: ctest connect model
	cd Extraction && $(MAKE);

clean:
	cd Connect && $(MAKE) clean
	cd Model && $(MAKE) clean
	cd Extraction && $(MAKE) clean
	cd ctest && $(MAKE) clean
