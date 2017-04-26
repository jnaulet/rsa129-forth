\ Miller-Rabin primality test (64-bit)
: a ( n -- 2 < a < n-2 ) 26 ;
: x ( n d -- x )
    \ n d -- over
    \ n d n -- a
    \ n d a -- swap
    \ n a d -- pow
    \ n a^d -- swap
    \ a^d n -- mod
    \ x
    over a swap pow swap mod ;

: p2fact ( n -- d r )
    \ n -- 64 0 do
    \ d -- dup
    \ d d -- ?odd
    \ d b -- if then
    \ d -- i
    \ d r -- leave
    \
    \ d -- 2/
    \ d -- loop
    63 0 do dup ?odd if i leave then 2/ loop ;

: compx ( x n -- x )
    \ x n -- swap
    \ n x -- square
    \ n x^2 -- swap
    \ x^2 n -- mod
    \ x
    swap square swap mod ;

: ?composite ( n x r -- bool )
    \ n x r -- 1-
    \ n x r-1 -- 0 do
    \ n x -- over
    \ n x n -- compx
    \ n x -- dup
    \ n x x -- 1 =
    \ n x b -- if
    \ n x -- 2drop 1
    \ 1 -- leave
    \
    \ n x -- 2dup
    \ n x n x -- swap
    \ n x x n -- 1-
    \ n x x n-1 -- =
    \ n x b -- if then
    \ n x -- 2drop 0
    \ 0 -- leave
    \
    \ n x -- loop
    \ n x -- 2drop
    \ -- 1
    \ 1
    1- 0 do over compx dup
	1 = if 2drop 1 leave then 2dup swap
	1- = if 2drop 0 leave then
    loop 2drop 1 ;

: ?witness ( x n -- bool )
    \ x n -- over
    \ x n x -- swap
    \ x x n -- 1-
    \ x x n-1 -- =
    \ x b -- swap
    \ b x -- 1 =
    \ b b -- or
    \ b
    over swap 1- = swap 1 = or ;

: ?prime ( n k -- bool )
    \ n k -- over
    \ n k n -- 1-
    \ n k n-1 -- p2fact
    \ n k d r -- rot
    \ n d r k -- 0 do
    \ n d r -- 2over
    \ n d r n d -- over
    \ n d r n d n -- swap
    \ n d r n n d -- x
    \ n d r n x -- over over swap
    \ n d r n x x n -- ?witness
    \ n d r n x b -- if then
    \ n d r n x -- 2drop
    \ else
    \ n d r n x -- 2over
    \ n d r n x r n -- rot
    \ n d r n n x r -- ?composite
    \ n d r n b -- if then
    \ n d r n -- 2drop 2drop 0
    \ 0 -- leave
    \ n d r n -- drop
    \ n d r -- loop
    
    \ n d r n d r n -- rot
    \ n d r n r n d -- x
    \ n d r n r x -- 2over
    \ n d r n r x n r -- drop
    \ n d r n r x n -- ?contwitness
    \ n d r n r b -- if then
    \ n d r n r x -- dup
    \ n d r n r x x -- 1 =
    \ n d r n r x b -- if then
    \ n d r n r x -- 2drop drop
    \ n d r -- else
    \ n d r n r x -- swap
    \ n d r n x r -- ?composite
    \ n d r b -- if then
    \ n d r -- 2drop drop 0
    \ 0 -- leave
    \
    \ n d r -- loop 2drop drop 1
    \ 1
    over 1- p2fact rot
    0 do 2over over swap x over over swap
	?witness if 2drop else
	    2over rot ?composite if 2drop 2drop 0 leave then drop
	then
    loop 2drop drop 1 ;
