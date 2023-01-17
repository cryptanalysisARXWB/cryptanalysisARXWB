all: fast_implicit.so

clean:
	rm -f fast_implicit.so white_box_arx.so


fast_implicit.so: fast_implicit.c
	$(CC) -fPIC fast_implicit.c -shared -o fast_implicit.so -O3