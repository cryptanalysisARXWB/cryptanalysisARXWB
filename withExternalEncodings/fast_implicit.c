#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

struct uint256_t {
	__uint128_t lo;
	__uint128_t hi;
};

uint32_t solve32(uint32_t y, uint64_t *base_mat, uint64_t* MS, int32_t block_size, int32_t n_rows) {
	// MS[n_blocks][2**block_size][n_rows]
	uint32_t mask = (1ull << block_size) - 1;
	assert(32 % block_size == 0);
	int n_blocks = 32/block_size;
	uint32_t max_block = mask + 1;

	uint64_t *matrix = calloc(n_rows, sizeof(uint64_t));
	if (!matrix) {
		perror("malloc");
		fprintf(stderr, "malloc failed\n");
		return 0;
	}
	memcpy(matrix, base_mat, n_rows * sizeof(uint64_t));
	for (int i = 0; i < n_blocks; i++) {
		uint64_t *ptr = MS + i * max_block * n_rows + (y & mask) * n_rows;
		// ptr = MS[i][y & mask]
		for (int j = 0; j < n_rows; j++) {
			matrix[j] ^= ptr[j];
		}
		y >>= block_size;
	}

	for (int i = 0; i < 32; i++) {
		int found = 0;
		uint64_t row;
		for (int j = n_rows-1; j >= i; j--) {
			row = matrix[j];
			if ((row >> (63-i)) & 1) {
				matrix[j] = matrix[i];
				matrix[i] = row;
				found = 1;
				break;
			}
		}
		if (!found) {
			fprintf(stderr, "pivot failed\n");
			goto fail;
		}

		for (int j = 0; j < n_rows; j++) {
			if (j == i) {
				continue;
			}
			if ((matrix[j] >> (63 - i)) & 1) {
				matrix[j] ^= row;
			}
		}
	}

	uint32_t x = 0;
	for (int i = 0; i < 32; i++) {
		uint32_t bit = matrix[i] & 1;
		// printf("i %2d matrix %016lx\n", i, matrix[i]);
		x |= bit << (32-1-i);
	}
	for (int i = 32; i < n_rows; i++) {
		// printf("i %2d matrix %016lx\n", i, matrix[i]);
		if (matrix[i]) {
			printf("insolvable...\n");
			goto fail;
		}
	}
	return x;

fail:
	free(matrix);
	return 0;
}

uint64_t solve64(uint64_t y, __uint128_t *base_mat, __uint128_t* MS, int32_t block_size, int32_t n_rows) {
	// MS[n_blocks][2**block_size][n_rows]
	uint64_t mask = (1ull << block_size) - 1;
	assert (64 % block_size == 0);
	int n_blocks = 64/block_size;
	uint64_t max_block = mask + 1;

	__uint128_t *matrix = calloc(n_rows, sizeof(__uint128_t));
	if (!matrix) {
		perror("malloc");
		fprintf(stderr, "malloc failed\n");
		return 0;
	}
	memcpy(matrix, base_mat, n_rows * sizeof(__uint128_t));
	for (int i = 0; i < n_blocks; i++) {
		__uint128_t *ptr = MS + i * max_block * n_rows + (y & mask) * n_rows;
		// ptr = MS[i][y & mask]
		for (int j = 0; j < n_rows; j++) {
			matrix[j] ^= ptr[j];
		}
		y >>= block_size;
	}

	for (int i = 0; i < 64; i++) {
		int found = 0;
		__uint128_t row;
		for (int j = n_rows-1; j >= i; j--) {
			row = matrix[j];
			if ((row >> (127-i)) & 1) {
				matrix[j] = matrix[i];
				matrix[i] = row;
				found = 1;
				break;
			}
		}
		if (!found) {
			fprintf(stderr, "pivot failed\n");
			goto fail;
		}

		for (int j = 0; j < n_rows; j++) {
			if (j == i) {
				continue;
			}
			if ((matrix[j] >> (127 - i)) & 1) {
				matrix[j] ^= row;
			}
		}
	}

	uint64_t x = 0;
	for (int i = 0; i < 64; i++) {
		uint64_t bit = matrix[i] & 1;
		// printf("i %2d matrix %016lx\n", i, matrix[i]);
		x |= bit << (63-i);
	}
	for (int i = 64; i < n_rows; i++) {
		// printf("i %2d matrix %016lx\n", i, matrix[i]);
		if (matrix[i]) {
			printf("insolvable...\n");
			goto fail;
		}
	}
	return x;

fail:
	free(matrix);
	return 0;
}

__uint128_t solve128(__uint128_t y, struct uint256_t *base_mat, struct uint256_t* MS, int32_t block_size, int32_t n_rows) {
	// MS[n_blocks][2**block_size][n_rows]
	__uint128_t mask = (1ull << block_size) - 1;
	assert (128 % block_size == 0);
	int n_blocks = 128/block_size;
	__uint128_t max_block = mask + 1;

	struct uint256_t *matrix = calloc(n_rows, sizeof(struct uint256_t));
	if (!matrix) {
		perror("malloc");
		fprintf(stderr, "malloc failed\n");
		return 0;
	}
	memcpy(matrix, base_mat, n_rows * sizeof(struct uint256_t));
	for (int i = 0; i < n_blocks; i++) {
		struct uint256_t *ptr = MS + i * max_block * n_rows + (y & mask) * n_rows;
		// ptr = MS[i][y & mask]
		for (int j = 0; j < n_rows; j++) {
			matrix[j].lo ^= ptr[j].lo;
			matrix[j].hi ^= ptr[j].hi;
		}
		y >>= block_size;
	}

	for (int i = 0; i < 128; i++) {
		int found = 0;
		struct uint256_t row;
		for (int j = n_rows-1; j >= i; j--) {
			row.lo = matrix[j].lo;
			row.hi = matrix[j].hi;
			// printf("trying pivot for %3d: %3d : %016lx %016lx %016lx %016lx\n",
			// 	i, j,
			// 	(uint64_t)(row.lo),
			// 	(uint64_t)(row.lo >> 64),
			// 	(uint64_t)(row.hi),
			// 	(uint64_t)(row.hi >> 64)
			// );

			if ((row.hi >> (127-i)) & 1) {
				matrix[j].lo = matrix[i].lo;
				matrix[j].hi = matrix[i].hi;
				matrix[i].lo = row.lo;
				matrix[i].hi = row.hi;
				found = 1;
				break;
			}
		}
		if (!found) {
			fprintf(stderr, "pivot failed\n");
			goto fail;
		}

		for (int j = 0; j < n_rows; j++) {
			if (j == i) {
				continue;
			}
			if ((matrix[j].hi >> (127 - i)) & 1) {
				matrix[j].lo ^= row.lo;
				matrix[j].hi ^= row.hi;
			}
		}
	}

	__uint128_t x = 0;
	for (int i = 0; i < 128; i++) {
		__uint128_t bit = matrix[i].lo & 1;
		// printf("i %2d matrix %016lx\n", i, matrix[i]);
		x |= bit << (127-i);
	}
	for (int i = 128; i < n_rows; i++) {
		// printf("i %2d matrix %016lx\n", i, matrix[i]);
		if (matrix[i].lo || matrix[i].hi) {
			printf("insolvable...\n");
			goto fail;
		}
	}
	return x;

fail:
	free(matrix);
	return 0;
}