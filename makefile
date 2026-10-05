all: caxx paxx

caxx: caxx.c
	gcc -o caxx caxx.c -lm -lquadmath -O2
paxx: axx.py
	chmod +x axx.py
install:
	sudo cp axx.py paxx
	sudo cp axx.py axx
	sudo cp paxx /usr/local/bin/paxx
	sudo cp axx.1.gz /usr/share/man/man1/
	sudo cp caxx /usr/local/bin/caxx
