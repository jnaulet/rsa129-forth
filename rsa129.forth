// RSA-129 crack FORTH implementation
// 114 381 625 757 888 867 669 235 779 976 146 612 010 218 296 721 242 362 562 561 842 935 706 935 245 733 897 830 597 123 563 958 705 058 989 075 147 599 290 026 879 543 541

// Simple math ops
: pow2+ ( n p -- n^p where p>1 )
  over swap 1 do over * loop swap drop ;
: pow ( n p -- n^p )
  dup 1 > if pow2+ else drop then ;
: square ( n -- n^2) dup * ;
: ?odd ( n -- odd ) 1 and ;

// Miller-Rabin primality test (64-bit)
: a ( n -- 2 < a < n-1 ) 26 ;
: x ( n r d -- x )
  rot 2over a swap pow swap mod rot 2drop ;
  
: p2fact ( n -- r d )
  64 0 do dup ?odd if i leave then 2/ loop ;

: ?prime ( n k -- bool )
// n k -- over
// n k n -- 1-
// n k n-1 -- p2fact
// n k r d -- rot
// n r d k -- 0 do
// n r d -- x
// x
  over 1- p2fact rot 0 do 