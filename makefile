all: caxx paxx

caxx: caxx.c
	gcc -o caxx caxx.c -lm -O2
	sudo cp caxx /usr/bin/caxx
paxx: axx.py
	sudo chmod +x axx.py
	sudo cp axx.py paxx
	sudo cp axx.py axx
	sudo cp paxx /usr/bin/paxx
