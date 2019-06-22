#include <cpuid.h>
#include <iostream>
#include <vector>
#include <array>
#include <set>

// Automata theory // An algorithmic approach
// https://www7.in.tum.de/~esparza/autoskript.pdf - Chapter 10: Applications III - presburger arithmetic

// https://www7.in.tum.de/um/courses/auto/ws1718/slides1718/09-Presburger_Arithmetic.pdf
using namespace std;

typedef int v4si __attribute__ ((vector_size (16)));

// https://github.com/ekmett/coda/blob/master/src/automata/Automata/NFA.hs
// https://github.com/ekmett/coda/blob/master/src/automata/Automata/Internal.hs
// https://github.com/ekmett/coda/blob/master/src/automata/Automata/Presburger.hs

bool avxSupported = false;

// T = type of numbers to use
// S = number of states, I = number of inputs
// A = automata class
template<int S>
struct A { 
    // transition table. S x Bool -> S
    int t[S][2];
    // encodes whether the state f[i] is a final state.
    bool f[S];
};

A<1> universe() {
    A<1> a;
    a.t[0][0] = 0; // loops back
    a.t[0][1] = 0; // loops back
    a.f[0] = true;
    return a;
}

A<1> empty() {
    A<1> a;
    a.t[0][0] = 0; // loops back
    a.t[0][1] = 0; // loops back
    a.f[0] = false;
    return a;
}

template<int n>
void complement(A<n> &a) {
    #pragma omp simd
    for(int i = 0; i < n; ++i) 
        a.f[i] = !a.f[i];
}

// nondeterministic automata
template<int S>
struct NA {
    // a relation S x {0, 1, 2==epsilon} ~ S
    bool t[S][3][S];
    // final state?
    bool f[S];

    // check if deterministic
    bool isd() {
    }

    //universe
    static inline NA<1> univ() {
        NA<1> x;
        x.t[0][0][0] = true;
        x.t[0][1][0] = true;
        x.t[0][2][0] = true;
        x.f[0] = true;
        return x;
    }

    static inline NA<1> empty() {
        NA<1> x = NA<1>::univ();
        x.c();
        return x;
    }
    

    //complement
    void inline c() {
        for(int i = 0; i < S; ++i) f[i] = !f[i];
    }
};

template<int N, int M>
NA<N+M> u(NA<N> n, NA<M> m) {
    NA<1+N+M> x;
    for(int i = 0; i < n; ++i) {
        x.f[1+i] = n.f[i];
    }

    for(int i = 0; i < M; ++i) {
        x.f[1+N+i] = m.f[i];
    }

    // epsilon transition to first state of N
    x.f[0][2][1] = true;
    // epsilon transition to first state of M
    x.f[0][2][N+1] = true;

    // copy states
    for(int i = 0; i < N; ++i) {
        for(int j = 0; j < 3; ++j) {
            for(int k = 0; k < N; ++k) {
                x.f[1+i][j][1+k] = n.f[i][j][k];
            }

        }
    }

    for(int i = 0; i < M; ++i) {
        for(int j = 0; j < 3; ++j) {
            for(int k = 0; k < M; ++k) {
                x.f[1+N+i][j][1+N+k] = n.f[i][j][k];
            }

        }
    }

    return x;
}


// machine accepting # a1x1 + a2x2 + ... anxn <= b 
// ie: a . x <= b (where x0, x1, ... xn are variables ∈ N)
// and (a1, a2, ... an, y) in Z.
auto add(vector<int> as, int b) {
	// transition function: Notation from book: Automata theory -- an algorithmic approach
	// states: Integers	
	// State q recognizes tuples of c ∈ N^k such that a . c <= q

	// Given state q and  a letter zeta ∈ {0,1}^n, A word w' ∈ ({0,1}^n)* is accepted
	// from q' iff the word (zeta:w') is accepted from q.
	// since we are encoding with LSB first,
	//     zeta:w' = zeta + 2 c'. where c' ∈ N^n is encoded by w' ∈ ({0, 1}^n)*.
	// 

	// q ACCEPT (zeta:w') <==> q' ACCEPT w'
	// q ACCEPT (zeta + 2c') <==> q' ACCEPT c'

	// q ACCEPT (zeta + 2c') ==> a . (zeta + 2c') <= q
	// q' ACCEPT c' ==> a. c' <= q'
	// a . (zeta + 2c' <= q) <==> a . (zeta + c' <= q')

	// a zeta + 2a . c' <= q
	// a zeta + 2q' <= q
	// 2q' <= q - a zeta
	// q' = (q - a . zeta) / 2
	return [&](int q, vector<bool> zeta) {
		int a = 0;
		for(int i = 0; i < as.size(); ++i) a += as[i] * zeta[i];
		return (q - a) / 2;
	};
}

int main() {

    return 0;
}
