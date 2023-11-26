@i
M = 0

// ---------------------------------- Drawing the first horizontal line ----------------------------------
(LOOP_HL_ONE)
  @i
  D = M;
  @8
  D = D - A;

  @FOR_LOOP_END_ONE
  D; JGE

  // Paint the pixels
  @i
  D = M;
  @SCREEN
  A = A + D;
  M = -1;

  // Move to the right
  @1
  D = A;
  @i
  M = M + D;

  @LOOP_HL_ONE
  0; JMP
(FOR_LOOP_END_ONE)


// ---------------------------------- Drawing the first vertical line ----------------------------------
(LOOP_VL_ONE)
  @i
  D = M;
  @4104
  D = D - A;

  @FOR_LOOP_END_TWO
  D; JGE

  @i
  D = M;
  @SCREEN
  A = A + D;
  M = 1;

  @32
  D = A;
  @i
  M = M + D;

  @LOOP_VL_ONE
  0; JMP
(FOR_LOOP_END_TWO)

// ---------------------------------- Drawing the second horizontal line ----------------------------------
(LOOP_HL_TWO)
  @i
  D = M;
  @4096
  D = A - D;

  @FOR_LOOP_END_THREE
  D; JGE

  // Move to the left
  @1
  D = A;
  @i
  M = M - D;

  // Paint the pixels
  @i
  D = M;
  @SCREEN
  A = A + D;
  M = -1;

  @LOOP_HL_TWO
  0; JMP
(FOR_LOOP_END_THREE)

// Move out of the last pixel's box
@32
D = A;
@i
M = M - D;

// ---------------------------------- Drawing the second vertical line ----------------------------------
(LOOP_VL_TWO)
  @i
  D = M;
  @0
  D = A - D;

  @FOR_LOOP_END_FOUR
  D; JGE

  @i
  D = M;
  @SCREEN
  A = A + D;
  M = 1;

  @32
  D = A;
  @i
  M = M - D;

  @LOOP_VL_TWO
  0; JMP
(FOR_LOOP_END_FOUR)

@i
M = 0
D = 0

// ---------------------------------- Drawing the first diagonal line ----------------------------------

(END)
@END
0; JMP

  
  

  