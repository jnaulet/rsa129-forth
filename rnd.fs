\ pseudo-random number generation
\ John Von Neumann middle-square method

include math.fs

variable rndseed

: mid32 ( n -- n )
    16 rshift 0xffffffff and ;

: seed ( n -- ) \ full 32-bit seed required
    rndseed ! ;

: random ( -- n )
    \ -- rndseed @
    \ n -- square
    \ n -- mid32
    \ n -- dup
    \ n n -- seed
    \ n
    rndseed @ square mid32 dup rndseed ! ;

: rndlimit ( m n -- r ) \ min max
    \ m n -- swap
    \ n m -- random
    \ n m r -- +
    \ m r+n -- swap
    \ r+n m -- mod
    \ r
    swap random + swap mod ;
