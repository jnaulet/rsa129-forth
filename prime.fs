\ Miller-Rabin primality test
include rnd.fs

variable n
variable r
variable d

\ Setup 
: p2fact ( n -- d r )
    \ n -- 63 0 do
    \ d -- dup
    \ d d -- ?odd
    \ d f -- if
    \ d -- i
    \ d r -- leave
    \ -- then
    \ d -- 2/
    \ d -- loop
    63 0 do dup ?odd if i leave then 2/ loop ;

: setnrd ( n -- )
    \ n -- dup
    \ n n -- !
    \ n -- 1-
    \ n-1 -- p2fact
    \ d r -- ! !
    \
    dup n ! 1- p2fact r ! d ! ;

: primesetup ( n -- )
    \ setup (FIXME)
    0x12345678 seed setnrd ;

\ Intermediate
: ?witness ( x n -- f )
    \ x n -- 1-
    \ x n-1  -- over
    \ x n-1 x -- =
    \ x f -- swap
    \ f x -- 1 =
    \ f b -- or
    \ b
    1- over = swap 1 = or ;

: x2modn ( x n -- x )
    \ x n -- swap
    \ n x -- square
    \ n x^2 -- swap
    \ x^2 n -- mod
    \ x
    swap square swap mod ;

variable ret

: ?composite1+ ( n x r-1 -- f )
    \ n x r-1 -- 1 ret !
    \ n x r-1 -- 0 do
    \ n x -- over
    \ n x n -- x2modn
    \ n x -- dup
    \ n x x -- 1 =
    \ n x f -- if
    \ n x -- 1 ret !
    \ n x -- leave
    \ -- then
    \ n x -- 2dup
    \ n x n x -- 1+
    \ n x n x+1 -- =
    \ n x f -- if
    \ n x -- 0 ret !
    \ n x -- leave
    \ -- then
    \ n x -- loop 2drop ret @
    \ f
    1 ret ! 0 do over x2modn dup
      1 = if 1 ret ! leave then
      2dup 1+ = if 0 ret ! leave then
    loop 2drop ret @ ;

: ?composite ( n x r -- f )
    \ n x r -- 1-
    \ n x r-1 -- dup
    \ n x r-1 r-1 -- 0>
    \ n x r-1 f -- if
    \ n x r-1 -- ?composite1+
    \ f -- else
    \ n x r-1 -- 2drop drop 1
    \ 1
    1- dup 0> if ?composite1+ else 2drop drop 1 then ;

: a ( n -- 2 < a < n-2 )
    2 - 2 swap rndlimit ;

: x ( n d -- x )
    \ n d -- over
    \ n d n -- a
    \ n d a -- swap
    \ n a d -- pow
    \ n a^d -- swap
    \ a^d n -- mod
    \ x
    over a swap pow swap mod ;

\ Main algorithm
: ?prime ( k n -- f )
    \ k n -- primesetup 1 ret !
    \ k -- 0 do n @ dup d @
    \ n n d -- x
    \ n x -- dup
    \ n x x -- rot
    \ x x n -- ?witness
    \ x f -- if
    \ x -- drop
    \ --
    \ x -- else
    \ x -- r @ n @
    \ x r n -- -rot
    \ n x r -- ?composite
    \ f -- if
    \ -- 0 leave
    \ 0 -- then
    \ -- then
    \ -- loop ret @
    \ f
    primesetup 1 ret ! \ FIXME
    0 do n @ dup d @ x dup rot
      ?witness if drop else r @ n @ -rot
        ?composite if 0 ret ! leave then
    then
    loop ret @ ; \ probably prime here
