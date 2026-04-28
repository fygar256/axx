all: caxx paxx

caxx: caxx.c
	gcc -o caxx caxx.c -lm -O2
	sudo cp caxx /usr/local/bin/caxx
paxx: axx.py
	sudo cp axx.py paxx
	sudo cp paxx /usr/local/bin/paxx
