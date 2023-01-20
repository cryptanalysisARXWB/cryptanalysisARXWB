from sage.all import *
from sage.all import (
    vector, random_vector,
    random_matrix, identity_matrix, matrix, block_matrix,
    GF, GL, ZZ,
    copy, Combinations,
)
from random import choice, randrange
from binteger import Bin  # sage -pip install binteger  # (note it's big-endian...)
from itertools import combinations, product
from collections import Counter, defaultdict
from tqdm import tqdm
from time import time

from attack_state import AttackState, DecompositionFail
from maps import AffineMap

# distinguishing 0.25 from 0.5
# lb: number of ones below which
#     we are sure it's not 0.5
LB = [None, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 9, 10, 10, 10, 10, 11, 11, 11, 12, 12, 12, 12, 13, 13, 13, 14, 14, 14, 15, 15, 15, 15, 16, 16, 16, 17, 17, 17, 18, 18, 18, 19, 19, 19, 20, 20, 20, 20, 21, 21, 21, 22, 22, 22, 23, 23, 23, 24, 24, 24, 25, 25, 25, 26, 26, 26, 27, 27, 27, 28, 28, 28, 29, 29, 29, 30, 30, 30, 31, 31, 31, 32, 32, 32, 33, 33, 33, 34, 34, 34, 35, 35, 36, 36, 36, 37, 37, 37, 38, 38, 38, 39, 39, 39, 40, 40, 40, 41, 41, 41, 42, 42, 43, 43, 43, 44, 44, 44, 45, 45, 45, 46, 46, 46, 47, 47, 48, 48, 48, 49, 49, 49, 50, 50, 50, 51, 51, 52, 52, 52, 53, 53, 53, 54, 54, 54, 55, 55, 56, 56, 56, 57, 57, 57, 58, 58, 59, 59, 59, 60, 60, 60, 61, 61, 61, 62, 62, 63, 63, 63, 64, 64, 64, 65, 65, 66, 66, 66, 67, 67, 67, 68, 68, 69, 69, 69, 70, 70, 71, 71, 71, 72, 72, 72, 73, 73, 74, 74, 74, 75, 75, 75, 76, 76, 77, 77, 77, 78, 78, 79, 79, 79, 80, 80, 80, 81, 81, 82, 82, 82, 83, 83, 84, 84, 84, 85, 85, 85, 86, 86, 87, 87, 87, 88, 88, 89, 89, 89, 90, 90, 90, 91, 91, 92, 92, 92, 93, 93, 94, 94, 94, 95, 95, 96, 96, 96, 97, 97, 98, 98, 98, 99, 99, 99, 100, 100, 101, 101, 101, 102, 102, 103, 103, 103, 104, 104, 105, 105, 105, 106, 106, 107, 107, 107, 108, 108, 109, 109, 109, 110, 110, 111, 111, 111, 112, 112, 113, 113, 113, 114, 114, 115, 115, 115, 116, 116, 117, 117, 117, 118, 118, 119, 119, 119, 120, 120, 121, 121, 121, 122, 122, 123, 123, 123, 124, 124, 125, 125, 125, 126, 126, 127, 127, 127, 128, 128, 129, 129, 129, 130, 130, 131, 131, 131, 132, 132, 133, 133, 133, 134, 134, 135, 135, 135, 136, 136, 137, 137, 137, 138, 138, 139, 139, 140, 140, 140, 141, 141, 142, 142, 142, 143, 143, 144, 144, 144, 145, 145, 146, 146, 146, 147, 147, 148, 148, 148, 149, 149, 150, 150, 151, 151, 151, 152, 152, 153, 153, 153, 154, 154, 155, 155, 155, 156, 156, 157, 157, 158, 158, 158, 159, 159, 160, 160, 160, 161, 161, 162, 162, 162, 163, 163, 164, 164, 165, 165, 165, 166, 166, 167, 167, 167, 168, 168, 169, 169, 169, 170, 170, 171, 171, 172, 172, 172, 173, 173, 174, 174, 174, 175, 175, 176, 176, 177, 177, 177, 178, 178, 179, 179, 179, 180, 180, 181, 181, 181, 182, 182, 183, 183, 184, 184, 184, 185, 185, 186, 186, 186, 187, 187, 188, 188, 189, 189, 189, 190, 190, 191, 191, 191, 192, 192, 193, 193, 194, 194, 194, 195, 195, 196, 196, 197, 197, 197, 198, 198, 199, 199, 199, 200, 200, 201, 201, 202, 202, 202, 203, 203, 204, 204, 204, 205, 205, 206, 206, 207, 207, 207, 208, 208, 209, 209, 210, 210, 210, 211, 211, 212, 212, 212, 213, 213, 214, 214, 215, 215, 215, 216, 216, 217, 217, 218, 218, 218, 219, 219, 220, 220, 220, 221, 221, 222, 222, 223, 223, 223, 224, 224, 225, 225, 226, 226, 226, 227, 227, 228, 228, 229, 229, 229, 230, 230, 231, 231, 231, 232, 232, 233, 233, 234, 234, 234, 235, 235, 236, 236, 237, 237, 237, 238, 238, 239, 239, 240, 240, 240, 241, 241, 242, 242, 243, 243, 243, 244, 244, 245, 245, 246, 246, 246, 247, 247, 248, 248, 248, 249, 249, 250, 250, 251, 251, 251, 252, 252, 253, 253, 254, 254, 254, 255, 255, 256, 256, 257, 257, 257, 258, 258, 259, 259, 260, 260, 260, 261, 261, 262, 262, 263, 263, 263, 264, 264, 265, 265, 266, 266, 266, 267, 267, 268, 268, 269, 269, 269, 270, 270, 271, 271, 272, 272, 272, 273, 273, 274, 274, 275, 275, 275, 276, 276, 277, 277, 278, 278, 278, 279, 279, 280, 280, 281, 281, 281, 282, 282, 283, 283, 284, 284, 284, 285, 285, 286, 286, 287, 287, 287, 288, 288, 289, 289, 290, 290, 290, 291, 291, 292, 292, 293, 293, 294, 294, 294, 295, 295, 296, 296, 297, 297, 297, 298, 298, 299, 299, 300, 300, 300, 301, 301, 302, 302, 303, 303, 303, 304, 304, 305, 305, 306, 306, 306, 307, 307, 308, 308, 309, 309, 309, 310, 310, 311, 311, 312, 312, 313, 313, 313, 314, 314, 315, 315, 316, 316, 316, 317, 317, 318, 318, 319, 319, 319, 320, 320, 321, 321, 322, 322, 322, 323, 323, 324, 324, 325, 325, 326, 326, 326, 327, 327, 328, 328, 329, 329, 329, 330, 330, 331, 331, 332, 332, 332, 333, 333, 334, 334, 335, 335, 336, 336, 336, 337, 337, 338, 338, 339, 339, 339, 340, 340, 341, 341, 342, 342, 342, 343, 343, 344, 344, 345, 345, 346, 346, 346, 347, 347, 348, 348, 349, 349, 349, 350, 350, 351, 351, 352, 352, 353, 353, 353, 354, 354, 355, 355, 356, 356, 356, 357, 357, 358, 358, 359, 359, 359, 360, 360, 361, 361, 362, 362, 363, 363, 363, 364, 364, 365, 365, 366, 366, 366, 367, 367, 368, 368, 369, 369, 370, 370, 370, 371, 371, 372, 372, 373, 373, 373, 374, 374, 375, 375, 376, 376]
# ub: number of ones above which
#     we are sure it's not 0.25
UB = [None, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 24, 25, 26, 27, 27, 28, 28, 29, 30, 30, 31, 32, 32, 33, 33, 34, 34, 35, 35, 36, 37, 37, 38, 38, 39, 39, 40, 40, 41, 41, 42, 42, 43, 43, 44, 44, 45, 45, 46, 46, 47, 47, 48, 48, 49, 49, 49, 50, 50, 51, 51, 52, 52, 53, 53, 54, 54, 55, 55, 55, 56, 56, 57, 57, 58, 58, 58, 59, 59, 60, 60, 61, 61, 62, 62, 62, 63, 63, 64, 64, 65, 65, 65, 66, 66, 67, 67, 67, 68, 68, 69, 69, 70, 70, 70, 71, 71, 72, 72, 72, 73, 73, 74, 74, 74, 75, 75, 76, 76, 76, 77, 77, 78, 78, 78, 79, 79, 80, 80, 80, 81, 81, 82, 82, 82, 83, 83, 84, 84, 84, 85, 85, 86, 86, 86, 87, 87, 88, 88, 88, 89, 89, 89, 90, 90, 91, 91, 91, 92, 92, 93, 93, 93, 94, 94, 94, 95, 95, 96, 96, 96, 97, 97, 97, 98, 98, 99, 99, 99, 100, 100, 100, 101, 101, 102, 102, 102, 103, 103, 103, 104, 104, 105, 105, 105, 106, 106, 106, 107, 107, 107, 108, 108, 109, 109, 109, 110, 110, 110, 111, 111, 112, 112, 112, 113, 113, 113, 114, 114, 114, 115, 115, 116, 116, 116, 117, 117, 117, 118, 118, 118, 119, 119, 119, 120, 120, 121, 121, 121, 122, 122, 122, 123, 123, 123, 124, 124, 124, 125, 125, 126, 126, 126, 127, 127, 127, 128, 128, 128, 129, 129, 129, 130, 130, 131, 131, 131, 132, 132, 132, 133, 133, 133, 134, 134, 134, 135, 135, 135, 136, 136, 136, 137, 137, 138, 138, 138, 139, 139, 139, 140, 140, 140, 141, 141, 141, 142, 142, 142, 143, 143, 143, 144, 144, 144, 145, 145, 146, 146, 146, 147, 147, 147, 148, 148, 148, 149, 149, 149, 150, 150, 150, 151, 151, 151, 152, 152, 152, 153, 153, 153, 154, 154, 154, 155, 155, 155, 156, 156, 157, 157, 157, 158, 158, 158, 159, 159, 159, 160, 160, 160, 161, 161, 161, 162, 162, 162, 163, 163, 163, 164, 164, 164, 165, 165, 165, 166, 166, 166, 167, 167, 167, 168, 168, 168, 169, 169, 169, 170, 170, 170, 171, 171, 171, 172, 172, 172, 173, 173, 173, 174, 174, 174, 175, 175, 175, 176, 176, 176, 177, 177, 177, 178, 178, 178, 179, 179, 179, 180, 180, 180, 181, 181, 181, 182, 182, 182, 183, 183, 183, 184, 184, 184, 185, 185, 185, 186, 186, 186, 187, 187, 187, 188, 188, 188, 189, 189, 189, 190, 190, 190, 191, 191, 191, 192, 192, 192, 193, 193, 193, 194, 194, 194, 195, 195, 195, 196, 196, 196, 197, 197, 197, 198, 198, 198, 199, 199, 199, 200, 200, 200, 201, 201, 201, 202, 202, 202, 203, 203, 203, 203, 204, 204, 204, 205, 205, 205, 206, 206, 206, 207, 207, 207, 208, 208, 208, 209, 209, 209, 210, 210, 210, 211, 211, 211, 212, 212, 212, 213, 213, 213, 214, 214, 214, 215, 215, 215, 216, 216, 216, 217, 217, 217, 217, 218, 218, 218, 219, 219, 219, 220, 220, 220, 221, 221, 221, 222, 222, 222, 223, 223, 223, 224, 224, 224, 225, 225, 225, 226, 226, 226, 227, 227, 227, 227, 228, 228, 228, 229, 229, 229, 230, 230, 230, 231, 231, 231, 232, 232, 232, 233, 233, 233, 234, 234, 234, 235, 235, 235, 235, 236, 236, 236, 237, 237, 237, 238, 238, 238, 239, 239, 239, 240, 240, 240, 241, 241, 241, 242, 242, 242, 243, 243, 243, 243, 244, 244, 244, 245, 245, 245, 246, 246, 246, 247, 247, 247, 248, 248, 248, 249, 249, 249, 250, 250, 250, 250, 251, 251, 251, 252, 252, 252, 253, 253, 253, 254, 254, 254, 255, 255, 255, 256, 256, 256, 256, 257, 257, 257, 258, 258, 258, 259, 259, 259, 260, 260, 260, 261, 261, 261, 262, 262, 262, 262, 263, 263, 263, 264, 264, 264, 265, 265, 265, 266, 266, 266, 267, 267, 267, 268, 268, 268, 268, 269, 269, 269, 270, 270, 270, 271, 271, 271, 272, 272, 272, 273, 273, 273, 273, 274, 274, 274, 275, 275, 275, 276, 276, 276, 277, 277, 277, 278, 278, 278, 278, 279, 279, 279, 280, 280, 280, 281, 281, 281, 282, 282, 282, 283, 283, 283, 283, 284, 284, 284, 285, 285, 285, 286, 286, 286, 287, 287, 287, 288, 288, 288, 288, 289, 289, 289, 290, 290, 290, 291, 291, 291, 292, 292, 292, 293, 293, 293, 293, 294, 294, 294, 295, 295, 295, 296, 296, 296, 297, 297, 297, 297, 298, 298, 298, 299, 299, 299, 300, 300, 300, 301, 301, 301, 302, 302, 302, 302, 303, 303, 303, 304, 304, 304, 305, 305, 305, 306, 306, 306, 306, 307, 307, 307, 308, 308, 308, 309, 309, 309, 310, 310, 310, 310, 311, 311, 311, 312, 312, 312, 313, 313, 313, 314, 314, 314, 315, 315, 315, 315, 316, 316, 316, 317, 317, 317, 318, 318, 318, 319, 319, 319, 319, 320, 320, 320, 321, 321, 321, 322, 322, 322, 323, 323, 323, 323, 324, 324, 324, 325, 325, 325, 326, 326, 326, 327, 327, 327, 327, 328, 328, 328, 329, 329, 329, 330, 330, 330, 330, 331, 331, 331, 332, 332, 332, 333, 333, 333, 334, 334, 334, 334, 335, 335, 335, 336, 336, 336, 337, 337, 337, 338, 338, 338, 338, 339, 339, 339, 340, 340, 340, 341, 341, 341, 342, 342, 342, 342, 343, 343, 343, 344, 344, 344, 345, 345, 345, 345, 346, 346, 346, 347, 347, 347, 348, 348, 348, 349, 349, 349, 349, 350, 350, 350, 351, 351, 351, 352, 352, 352, 352, 353, 353, 353, 354, 354, 354, 355, 355, 355, 356, 356, 356, 356, 357, 357, 357, 358, 358, 358, 359, 359, 359, 359, 360, 360, 360, 361, 361, 361, 362]




class RoundDecomposition:
    class Unsolvable(DecompositionFail):
        pass

    class UnsolvableA(Unsolvable):
        pass

    def __init__(self, n, state=None):
        self.n = int(n)
        self.N = 2*self.n

        self.state0 = self.state = state

        self.rpool = None
        self.rpool_state = None

    def recover_right_branch_space(self, *, skip_last=0, state=None):
        if state:
            self.state = state

        # 1. find affine I/O relations
        if skip_last == 0:
            # use random samples
            rows = [
                Bin.concat(x, y, 1, ns=(self.N, self.N, 1)).vector
                for x, y in self.state.sample(2*self.N + 33)
            ]
        else:
            # use random samples but ignore last bits to zero
            rows = []
            base = Bin.random(skip_last).resize(self.N)
            for _ in range(2*self.N + 33):
                x = Bin.random(self.N - skip_last).resize(self.N) << skip_last
                x = x ^ base
                y = self.state.query(x)
                #print(x)
                #print(y, end="\n\n")
                # hide relations on the skipped part
                x = x ^ Bin.random(skip_last).resize(self.N)
                y = y ^ Bin.random(skip_last).resize(self.N)
                vec = Bin.concat(x, y, 1).vector
                assert len(vec) == 2*self.N + 1
                rows.append(vec)

        mat = matrix(GF(2), rows)
        #assert mat.rank() == self.N + self.n

        # x, y, 1
        linrel = mat.right_kernel().matrix()
        ker_dim = linrel.nrows()
        #assert ker_dim
        #assert linrel.nrows() == self.n + 1

        # 2. Move n+1 equal bits aligned to the right (extend to invertible randomly)
        idlast = matrix(GF(2), skip_last, self.N)
        for i in range(skip_last):
            idlast[-1-i,-1-i] = 1

        modifX = self.ext_matrix_extract_left(linrel[:,:self.N], skip_last)
        modifY = self.ext_matrix_extract_left(linrel[:,self.N:2*self.N], skip_last)

        self.state = self.state.modified(
            projX=modifX,
            projY=modifY,
            cY=[0]*(self.N - ker_dim) + list(linrel.column(-1)),
        )
        #assert self.state.query_lr(0, 0b111)[1] == 0b111
        return ker_dim, linrel, self.state

    def ext_matrix_extract_left(self, rows, n_after):
        rows = matrix(GF(2), rows)
        assert rows.rank() == rows.nrows()
        n_rand = self.N - rows.nrows() - n_after

        dim = rows.nrows()
        idlast = matrix(GF(2), n_after, self.N)
        for i in range(n_after):
            idlast[-1-i,-1-i] = 1

        bot = matrix(GF(2), rows).stack(idlast)
        if bot.rank() == bot.nrows():
            for _ in range(64):
                rand = random_matrix(GF(2), self.N - dim - n_after, self.N)
                modif = rand.stack(bot)
                if modif.is_invertible():
                    return modif
        print("failed completing the following matrix with n_after =", n_after)
        #print(matrix(GF(2), rows).str())
        raise ZeroDivisionError("not completable extension")

    def random_input(self, zeroes=None): # mask=None, fix_quadratics=None):
        # if mask is None:
        #     mask = Bin.full(self.N)
        x = Bin.random(self.N) #& mask

        if zeroes:
            for i in zeroes:
                if x[i] == 1:
                    x ^= 1 << (x.n - 1 - i)
                assert x[i] == 0
        # if fix_quadratics:
        #     for i, j in fix_quadratics:
        #         if x[i] == x[j] == 1:
        #             if randrange(2):
        #                 x ^= 1 << (self.N - 1 - i)
        #             else:
        #                 x ^= 1 << (self.N - 1 - j)
        #         assert not (x[i] == x[j] == 1)
        return x

    def recover_outputs_by_degree(self, deg, *, state=None, skip_last=0, zero_sets=None):
        if state:
            self.state = state

        n, N = self.n, self.N

        d = deg + 1  # cube dimension

        rows = []
        while len(rows) < N + 32:
            #base = Bin.random(N)
            if zero_sets:
                zeroes = [choice(pair) for pair in zero_sets]
            else:
                zeroes = None

            base = self.random_input(zeroes=zeroes)
            while True:
                basis = [
                    self.random_input(zeroes=zeroes)
                    #Bin.random(N)
                    for i in range(d)
                ]
                if matrix([b.vector for b in basis]).rank() == d:
                    break

            data = []
            for pts in Combinations(basis):
                res = base
                for pt in pts:
                    res ^= pt
                data.append(res)

            ctsum = Bin.random(skip_last).resize(N)  # randomize ignored bits
            for pt in data:
                ctsum ^= self.state.query(pt)
            rows.append(ctsum)

        mat = matrix(GF(2), rows)
        #print("dim", d, ":", mat.nrows(), mat.ncols(), mat.rank(), "bits:", N-mat.rank())
        #rk = mat.right_kernel().matrix()
        linrel = mat.right_kernel().matrix()
        ker_dim = linrel.nrows()
        #print(rk)
        #print()
        #tn = rk.nrows()

        proj = self.ext_matrix_extract_left(linrel, skip_last)
        self.state = self.state.modified(projY=proj)
        return ker_dim, linrel, self.state

    def recover_left_to_triangular(self, state=None):
        if state:
            self.state = state

        print("recover_left_to_triangular")
        for i in tqdm(range(self.n-1)):
            max_rank = self.n - 1 - i

            # I: recover linear combination of Y equal to 1 on max rank
            while True:
                # dl = random n-1-i topmost bits (i lsbs are zero)
                chunk = randrange(2**max_rank)
                dl = Bin(chunk << i, self.n-1)
                rank, dys = self.sample_left_difference_rank(dl, max_rank)
                if rank == max_rank:
                    break

            soly = matrix(GF(2), dys).solve_right(vector(GF(2), [1]*len(dys)))
            # print("soly", soly)

            # II: recover linear combination of X equal to 1 on max rank
            dls = set()
            while True:
                # dl = random n-1-i topmost bits (i lsbs are zero)
                chunk = randrange(2**max_rank)
                dl = Bin(chunk << i, self.n-1)
                dy, _ = self.state.query_diff_lr(dl, 0)
                if dy.vector*soly:
                    dls.add(dl)
                    if len(dls) >= max_rank and matrix(GF(2), dls).rank() == max_rank:
                        break

            solx = matrix(GF(2), dls).solve_right(vector(GF(2), [1]*len(dls)))
            # print("solx", solx)

            # III: update projection maps (new state instance)
            jx, modifX = self.ext_matrix_set_bit(self.n-1-i-1, solx)
            jy, modifY = self.ext_matrix_set_bit(self.n-1-i-1, soly)

            prev = self.state
            self.state = self.state.modified(
                projX=modifX,
                projY=modifY,
            )
            # optimization: reuse pool
            # if i >= 1:
            #     for x, y in prev.pool:
            #         self.state.pool.append((Bin(modifX * x.vector), Bin(modifY * y.vector)))
        return self.state

    def sample_left_difference_rank(self, dl, max_rank):
        """
        Return rank of output differences and output differences.
        May underestimate rank due to undersampling.
        """
        rows = set()
        for i in range(max_rank + 40):
            dy, _ = self.state.query_diff_lr(dl, 0)
            rows.add(tuple(dy.vector))
            if i in (max_rank + 5, max_rank + 10):
                if matrix(GF(2), rows).rank() == max_rank:
                    return max_rank, rows
        return matrix(GF(2), rows).rank(), rows

    def ext_matrix_set_bit(self, i, sol):
        """Generate invertible matrix randomly mixing first i bits
        and setting bit indexed i to match linear combination given by `sol`,
        leaving all bits indexed i+1,... unmodified.
        """
        mod = identity_matrix(GF(2), self.N)
        for j in reversed(range(len(sol))):
            if sol[j]:
                mod[j] = mod[i]
                mod[i,:self.n-1] = sol
                break
        else:
            raise RuntimeError("should not happen")
        assert mod.is_invertible()
        return j, mod

    def recover_left_triangles(self, state=None):
        if state:
            self.state = state

        print("recover_left_triangles")
        for w in tqdm(range(3, self.n)):
            diff0 = 1            # 0b000...01
            diff1 = 1 + 2**(w-2) # 0b010...01

            #print("w =", w, ":", Bin(diff0), Bin(diff1))
            subdiagX = []
            subdiagY = []
            for i in (range( self.n-w)):
                st0 = Counter()
                st1 = Counter()

                msk = (2**w-1) << (self.N-w-i)
                itr = 0
                while True:
                    itr += 1
                    # TODO: query a 2-flat to get 2 pairs each
                    dy = self.state.query_diff(diff0 << (self.N-w-i))
                    st0[dy & msk] += 1
                    dy = self.state.query_diff(diff1 << (self.N-w-i))
                    st1[dy & msk] += 1

                    num0 = st0.most_common(1)[0][1]
                    num1 = st1.most_common(1)[0][1]
                    if itr >= len(LB) or (num0 <= LB[itr] and num1 <= LB[itr]):
                        lb = LB[itr] if itr < len(LB) else "-"
                        ub = UB[itr] if itr < len(UB) else "-"
                        print(
                            "!!! failed convergence",
                            f"w={w} i={i}",
                            "itr", itr,
                            "diffs", diff0, diff1, "|",
                            "LB-UB", lb, ub,
                        )
                        s0 = sorted(st0.values())
                        s1 = sorted(st1.values())
                        print(s0, s0[-1]/sum(s0), "total", sum(s0))
                        print(s1, s1[-1]/sum(s1), "total", sum(s1))
                        raise self.UnsolvableA("recover_left_triangles convergence failed")
                    elif num0 >= UB[itr]:
                        subdiagX.append(0)
                        diff = st0.most_common(1)[0][0]
                        subdiagY.append(diff[i+1])
                        break
                    elif num1 >= UB[itr]:
                        subdiagX.append(1)
                        diff = st1.most_common(1)[0][0]
                        subdiagY.append(diff[i+1])
                        break
            #print("diff", diff)
            #print("w", w, "subdiag", subdiagX, subdiagY)

            modifX = identity_matrix(GF(2), self.N)
            for i in range(self.n-w):
                modifX[i+1,i+2+w-3] = subdiagX[i]

            modifY = identity_matrix(GF(2), self.N)
            for i in range(self.n-w):
                modifY[i+1,i+2+w-3] = subdiagY[i]

            self.state = self.state.modified(
                projX=modifX,
                projY=modifY,
            )
        return self.state

    def recover_left_triangles_msb(self, state):
        if state:
            self.state = state
        rows = []
        target = []
        while True:
            for j in reversed(range(2, self.n-1)):
                dx = Bin.unit(j, self.N)
                dy = self.state.query_diff(dx)
                # if we have [MSB]1* then this one can affect MSB through
                # triangular linear maps or through addition itself
                # (which we can not distinguish)
                # so we look only at [MSB]0*
                if dy[1] == 1:
                    continue
                target.append(dy[0])
                rows.append(dx.list[1:self.n-1] + dy.list[1:self.n-1])

            mat = matrix(GF(2), rows)
            if mat.nrows() % 50 == 0:
                print(mat.nrows(), mat.ncols(), mat.rank()    )
            if mat.rank() == mat.ncols() - 3:
                break

        # the 3 undetermined bits (as linear masks on L,R)
        #- 2nd-to-MSB xor to MSB is unclear (each side)
        #- learnt only (LSBpt xor to MSB) ^ (LSBct xor to MSB)
        #- (3 bits unknown)
        (
            self.triangle_premsbX,
            self.triangle_lsbXY,
            self.triangle_premsbY,
        ) = list(mat.right_kernel().matrix())

        # mask for determined bits
        triangle_msb_fix = mat.solve_right(vector(target))

        self.state_pre3 = self.state
        self.state = self.state_fix_triangle_msb(self.state_pre3, triangle_msb_fix)  # can add any combination of the 3 rows above
        return self.state

    def state_fix_triangle_msb(self, state, maskXY):
        """Return AttackOracle with updated projections,
        adding linear function of n-2 middle bits of (l)
        to the MSB, at the input and at the output
        """
        n, N = self.n, self.N
        modifX = identity_matrix(GF(2), N)
        modifY = identity_matrix(GF(2), N)
        assert len(maskXY) == N-4
        modifX[0,1:n-1] = maskXY[:n-2]
        modifY[0,1:n-1] = maskXY[n-2:]

        return state.modified(
            projX=modifX,
            projY=modifY,
        )

    def get_ABC(self, state=None):
        if state:
            self.state = state

        n, N = self.n, self.N

        if self.rpool_state is not self.state:
            self.rpool = self.get_rpool()
            self.rpool_state = self.state

        while True:
            rows = []
            target = []
            for r, cands in self.rpool:
                rows.append(Bin(r, n+1).list + [1])

                # this leads to 2 MSB and 1 LSB rows zero  in B but seems ok??? until some later step..
                # A,B,C = sorted(cands, key=lambda abc:abc[1])[0]
                while True:
                    A,B,C = choice(list(cands))
                    # B = 0 works until some step
                    # but causes problems later.
                    if B:
                        break

                target.append(Bin.concat(A,B,C, n=n-1).vector)

            matR = matrix(GF(2), rows).transpose()
            matABC = matrix(GF(2), target).transpose()
            assert matR.rank() == n + 2

            ABCsol = matR.solve_left(matABC)
            assert ABCsol * matR == matABC

            A = ABCsol[:n-1]
            B = ABCsol[n-1:2*n-2]
            C = ABCsol[2*n-2:]
            if B.left_kernel():
                print("skipping singular B...")
                continue

            cA = Bin(A.column(-1))
            cB = Bin(B.column(-1))
            cC = Bin(C.column(-1))
            A = A[:,:-1]
            B = B[:,:-1]
            C = C[:,:-1]

            #print(block_matrix([[A,B,C]]).str())
            return A, B, C, cA, cB, cC

    def recover_ABC_remove_AC(self, state=None):
        if state:
            self.state = state

        n, N = self.n, self.N
        A, B, C, cA, cB, cC = self.get_ABC()

        # test MSB
        need_fix = False
        for _ in range(50):
            l0 = l = randrange(2**(n-1))
            r = Bin.random(n+1)
            ll, rr = self.state.query_lr(l, r)

            fA = A * r.vector + cA.vector
            fB = B * r.vector + cB.vector
            fC = C * r.vector + cC.vector

            mod = 2**(n-1)
            l = l0
            l ^= Bin(fA).int
            err = ((ll ^ Bin(fC)).int - l - Bin(fB).int) % mod
            if err not in (mod-1, 0, 1):
                need_fix = True
                break

        if need_fix:
            self.state = self.state_fix_triangle_msb(self.state, self.triangle_lsbXY)

        A, B, C, cA, cB, cC = self.get_ABC()

        modifX = block_matrix([
            [ZZ(1), A],
            [ZZ(0), ZZ(1)]
        ])
        modifY = block_matrix([
            [ZZ(1), C],
            [ZZ(0), ZZ(1)]
        ])
        self.state = self.state.modified(
            projX=modifX,
            cX=list(cA)+[0]*(n+1),
            projY=modifY,
            cY=list(cC)+[0]*(n+1),
        )
        return self.state, B, cB

    def get_rpool(self):
        print("generating pool of random (r) with 8 solutions for A,B,C values...", self.state)
        rrows = []
        rpool = []
        cur_rank = 0

        #with tqdm(total=self.n+2) as progress:
        if 1:
            while True:
                r = randrange(2**(self.n+1))

                new_row = Bin(r, self.n+1).list + [1]
                new_rank = matrix(GF(2), rrows + [new_row]).rank()
                if new_rank == cur_rank:
                    continue

                cands = self.ABC_cands_for_r(r)
                if not cands:
                    continue

                cur_rank = new_rank
                #progress.update(1)

                rrows.append(new_row)
                rpool.append((r, cands))

                if new_rank >= self.n + 2:
                    return rpool

    def ABC_cands_for_r(self, r):
        n, N = self.n, self.N

        data = []
        for _ in range(n+100):
            x = x0 = Bin.random(n-1)
            y, rr = self.state.query_lr(x, r)
            assert r == rr
            data.append((x0, y))

        m = 2
        mask = 2**m-1
        cands = set()
        for A, B, C in product(range(2**m), repeat=3):
            # NOTE: actually B = B + carry
            for x, y in data:
                test = ((x ^ A).int + B) ^ C
                if test & mask != y & mask:
                    break
            else:
                cands.add((A, B, C))

        #print("cands0", len(cands), "fs", f0, f1, f2)
        for m in range(3, n):
            assert cands
            cands2 = set()
            bit = 2**(m-1)
            mask = 2**m-1
            for A0, B0, C0 in cands:
                for a, b, c in product(range(2), repeat=3):
                    A = A0 + a * bit
                    B = B0 + b * bit
                    C = C0 + c * bit
                    for x, y in data:
                        test = ((x ^ A).int + B) ^ C
                        if test & mask != y & mask:
                            break
                    else:
                        cands2.add((A, B, C))
            # if m == h-1:
            #     print("m", m, "cands", len(cands), "->", len(cands2))

            cands = cands2
            if len(cands) > 8:
                #print("too many?", len(cands))
                return
            if not cands:
                print("failed somewhere before")
                raise
        return cands

    def recover_carry_sign(self, B, cB, state=None,):
        if state:
            self.state = state

        n, N = self.n, self.N
        mod = 2**(n-1)

        rows = []
        for _ in (range(3*self.n + 200)):
        # for _ in tqdm(range(3*self.n + 200)):
            l0 = l = randrange(2**(n-1))
            r = Bin.random(n+1)

            ll, rr = self.state.query_lr(l, r)
            fB = B * r.vector + cB.vector

            err = (ll.int - l - Bin(fB).int) % mod
            assert err in (mod-1, 0, 1)
            if err == mod - 1:
                rows.append(r)

        #print("errors ok!")

        # ad-hoc, just choose linear redundancy for vectors r
        # with error = -1
        mat = matrix(GF(2), [list(r) + [1] for r in rows])
        print("carry", -1, "rank", mat.rank(), "/", mat.ncols())
        assert mat.right_nullity() == 1  # this may fail?? todo: fix (more samples does not help?..)

        rk = mat.right_kernel()
        sol = rk.matrix()[0]
        #print("sol", sol)

        BB = copy(B)
        cBB = cB

        BB[-1] += sol[:-1]
        if sol[-1] == 0:
            cBB = cBB ^ 1

        if BB.rank() != BB.nrows():
            raise RuntimeError("Attack failed, choose another Bs")

        while True:
            rnd = random_matrix(GF(2), 2, BB.ncols())
            BBext = rnd.stack(BB)
            if BBext.is_invertible():
                break

        modif = block_matrix([
            [identity_matrix(n-1), ZZ(0)],
            [ZZ(0), BBext]
        ])
        cnst = vector([0] * (n+1) + list(cBB))
        self.state = self.state.modified(
            projX=modif,
            cX=cnst,
            projY=modif,
            cY=cnst,
        )
        return self.state

    def get_pseudocarry(self, r, state=None):
        if not state:
            state = self.state
        l0 = Bin.random(self.n-1)
        r = int(r)
        ll, rr = state.query_lr(l0, r)
        assert r == rr
        pc = (ll.int - l0.int - r) % 2**(self.n-1)
        assert pc in (0, 1)
        return pc

    def recover_carry(self, state=None):
        n, N = self.n, self.N
        if state:
            self.state = state

        # sample differences for r not affecting the pseudocarry
        rows = []
        n_tries = 0
        #with tqdm(total=self.n + 50) as progress:
        if 1:
            while len(rows) < n + 50:
                # Random linear combination hits carry with chance 7/8
                # (because there are 3 linear combinations involved...)
                # (2 real LSBs and a linear combination masking it)
                diff = Bin.random(n+1, nonzero=True)
                n_tries += 1
                for t in range(50):
                    r1 = Bin.random(n+1)
                    r2 = r1 ^ diff
                    c1 = self.get_pseudocarry(r1)
                    c2 = self.get_pseudocarry(r2)
                    if c1 != c2:
                        break
                else:
                    #progress.update(1)
                    rows.append(diff.list)

        mat = matrix(GF(2), rows)
        assert mat.rank() == mat.ncols() - 3 == n-2

        # find orthogonal subspace (3-dimensional)
        # i.e. linear combinations affecting the pseudocarry
        rk_incarry = mat.right_kernel().matrix()
        assert rk_incarry.nrows() == 3

        # calculate the mapping from these 3 affine bits to carry
        mp = {}
        while len(mp) != 8:
            r = Bin(randrange(2**(n+1)), n+1)
            pr = tuple(rk_incarry * r.vector)
            carry = self.get_pseudocarry(r)
            if pr in mp:
                assert mp[pr] == carry
            mp[pr] = carry

        mt = []
        for pr, carry in sorted(mp.items()):
            mt.append(pr + (carry,))
        mt = matrix(GF(2), mt)

        cols = mt[:,:-1].augment(matrix(8, 1, [1] * 8))
        affines = cols.column_space()
        # map from the value vector of any affine function to the
        # description in terms of the columns
        # (this is general, independent of pseudocarry)
        affines = {tuple(v): cols.solve_right(v) for v in affines}

        # check exhaustively all affine maps
        # such that
        #   pseudocarry = aff1(r) * aff2(r) + aff3(r)
        #   (shape guessed experimentally, need to prove)
        pseudocarry = mt.column(-1)
        tab = {tuple(vector(GF(2), aff3) + pseudocarry) for aff3 in affines}
        n_good = 0
        aff_sols = []
        for aff1, aff2 in combinations(affines, 2):
            mul = vector(GF(2), [a * b for a, b in zip(aff1, aff2)])
            if tuple(mul) in tab:
                aff3 = mul + pseudocarry
                sol1 = affines[tuple(aff1)]
                sol2 = affines[tuple(aff2)]
                sol3 = affines[tuple(aff3)]
                aff_sols.append((sol1, sol2, sol3))

                n_good += 1
        assert n_good == 12  # not necessary for recovery, but seems to be always 12?

        # choose any sol
        sol1, sol2, sol3 = choice(aff_sols)  # any sol is equivalen (does not help to make invertable later)

        # small test
        for _ in range(100):
            r = randrange(2**(n+1))
            pseudocarry = self.get_pseudocarry(r)

            vec = vector(GF(2), list(rk_incarry * Bin(r, n+1).vector) + [1])
            w1 = vec * sol1
            w2 = vec * sol2
            w3 = vec * sol3
            assert pseudocarry == w1 * w2 + w3

        # update projections
        x = identity_matrix(GF(2), N).augment(matrix(GF(2), N, 1))
        one = vector(GF(2), [0] * N + [1])

        rk0 = rk_incarry.augment(matrix(GF(2), 3, 1))
        ri = (rk0 * x[n-1:].stack(one)).stack(one)
        aff1 = sol1 * ri
        aff2 = sol2 * ri
        aff3 = sol3 * ri

        l = [
            x[i] + aff3 for i in range(n-1)
        ]
        llo = [
            aff1,
        ]
        r = [
            x[i] + aff3 for i in range(n+1,N)
        ]
        rlo = [
            aff2
        ]

        mod = matrix(GF(2), l + llo + r + rlo)

        modifX = copy(mod)
        modifX, cX = modifX[:,:-1], modifX.column(-1)

        modifY = copy(mod)
        modifY[n-1] += modifY[-1] # add r-lsb to l-lsb
        modifY, cY = modifY[:,:-1], modifY.column(-1)

        if modifX.is_singular():
            raise RuntimeError("failed to find invertible fix..")
        assert modifX.is_invertible(), modifX.rank()
        assert modifY.is_invertible(), modifY.rank()

        self.state = self.state.modified(
            projX=modifX,
            cX=cX,
            projY=modifY,
            cY=cY,
        )
        return self.state

    def recover_left_triangles_with_msb(self, state=None):
        if state:
            self.state = state

        state0 = self.state
        n_linear_bits, lin_masks, state1 = self.recover_right_branch_space(state=state0)
        state2 = self.recover_left_to_triangular(state1)
        state3 = self.recover_left_triangles(state2)
        state4 = self.recover_left_triangles_msb(state3)
        return state4

    def recover_all(self, state=None, num_tries=2):
        if state:
            self.state = state

        state0 = self.state
        n_linear_bits, lin_masks, state1 = self.recover_right_branch_space(state=state0)
        state2 = self.recover_left_to_triangular(state1)
        for itr in range(num_tries):
            try:
                state3 = self.recover_left_triangles(state2)
                state4 = self.recover_left_triangles_msb(state3)
                break
            except RuntimeError:
                print("failed affine decomposition attempt", itr, "/", num_tries)
        else:
            raise self.UnsolvableA("affine decomposition all attempts failed")

        while True:
            state5, B, cB = self.recover_ABC_remove_AC(state4)
            try:
                state6 = self.recover_carry_sign(B, cB, state5)
            except RuntimeError as err:
                print("choice B failed (recover_carry_sign), trying again..", err)
                continue

            try:
                state7 = self.recover_carry(state6)
            except RuntimeError as err:
                print("choice B failed (recover_carry), trying again..", err)
                continue

            break

        print("Success!")
        state7.mark_decomposed()
        return state7

    def recover_constants(self, state=None, n_bits=None):
        """Recovers XOR constants,
        Prerequisite: must implement (l+r, r) up to XOR const"""
        if state is not None:
            self.state = state

        n, N = self.n, self.N
        pool = []
        for x, y in self.state.sample(N):
            l, r = x.split(2)
            ll, rr = y.split(2)
            assert r == rr
            pool.append((l, r, ll, rr))

        sols = {(0,0,0)}
        if n_bits is None:
            n_bits = n
        for i in range(n_bits):
            mask = 2**(i+1) - 1
            sols2 = set()
            for a0, b0, c0 in sols:
                for a1, b1, c1 in product(range(2), repeat=3):
                    a = a0 + (a1 << i)
                    b = b0 + (b1 << i)
                    c = c0 + (c1 << i)

                    for l, r, ll, rr in pool:
                        l0 = l ^ a
                        r0 = r ^ b
                        rr ^= b
                        ll ^= c
                        assert r0 == rr
                        if (l0 + r0) & mask != ll & mask:
                            break
                    else:
                        sols2.add((a, b, c))

            sols = sols2
            if not (0 < len(sols) <= 4):
                return ()
        if len(sols) != 4:
            return ()
        return {(Bin(a, n), Bin(b, n), Bin(c, n)) for a, b, c in sols}
