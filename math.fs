\ Simple math ops
: pow2+ ( n p -- n^p where p>1 )
    \ n p -- over
    \ n p n -- swap
    \ n n p -- 1 do
    \ n n -- over
    \ n n n -- *
    \ n n^i -- loop
    \ n n^p -- swap
    \ n^p n -- drop
    \ n^p
    over swap 1 do over * loop swap drop ;

: pow ( n p -- n^p )
    \ n p -- dup
    \ n p p -- 1 > if then
    \ n p -- pow2+
    \ n^p
    \ else
    \ n p -- drop
    \ n^1
    dup 1 > if pow2+ else drop then ;

: square ( n -- n^2) dup * ;
: ?odd ( n -- f ) 1 and ;

\ Huge number functions
: div ( n ... n n -- n n ... n ) \ number div nwords -- result mod nwords
  0 do
