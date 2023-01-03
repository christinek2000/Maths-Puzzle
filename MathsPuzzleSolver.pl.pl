% ------------------ Program Purpose ------------------
% The program solves a "maths puzzle." A maths puzzle is a square grid of 
% squares with a header for each row and column (leftmost square in a row and 
% topmost square in a column). In addition, the puzzle meets the 
% following requirements:
        % 1. All squares in the grid other than the headers should be 
        %    a single digit from 1 to 9.
        % 2. Each row and column should have the same number of squares.
        % 3. Only the headers can be a number larger than a single digit
% The puzzle also meets the following constraints:
        % 1. No repeated digits in each row and each column
        % 2. Same value for all squares on the diagonal line 
        %    from the upper left corner to lower right corner
        % 3. The header of each row and column is either 
        %    the sum or the product of all the digits in that row or column
% The predicate puzzle_solution/1 is used to solve the maths puzzle. The user 
% enters a puzzle with most or all of the squares empty as the argument and the 
% program fills in all squares based on the requirements and constraints. 
% The program fails if the input puzzle cannot be solved.

% Assumptions: The argument of our puzzle solver predicate is a proper list of 
%              proper lists and all header squares are bound to integer. Also, 
%              there is at most one proper solution to a maths puzzle.

% ---------------- Data Structure ----------------
% The maths puzzle is a list of lists. Each list within the puzzle is a row and
% should all be the same length. The first list of the puzzle is the headers of 
% the columns and the first element of each list (except the first list) is the 
% header of the row. The first element of the first list is ignored. 

% ---------------- Library used ----------------
% Implemented the maths puzzle solver using constraint logic programming to set 
% the domain of unbounded variables in the puzzle and set constraints 
% that the puzzle should meet.
:- ensure_loaded(library(clpfd)).

% ---------------- Maths Puzzle Solver ----------------
% puzzle_solution(+Puzzle)

% puzzle_solution/1 takes a list of lists and checks the requirements and
% constraints for the maths puzzle.

% First, the solver checks if all the lists in the list are the same length. 
% Then, the solver uses transpose/2 to get the transposed puzzle. This is so 
% that the constraints for the columns can also be checked with the same 
% predicates used to check the constraints for the rows. The solver ensures that
% all squares other than the headers and the ignored corner square is a digit 
% from the domain 1 to 9 with domainConstraint/1.
% Then, checks constraint 1 to 3.
    % 1. Ensure no repeated digits in each row and column with allDistinct/1
    % 2. Ensure the diagonal squares are unified with diagonalUnification/1, 
    % 3. Ensure the header is the sum or product of the row or column with 
    %    headerConstraint/1
% groundRow/2 is used to ensure that each row is ground

puzzle_solution(Puzzle) :-
    maplist(same_length(Puzzle), Puzzle),
    
    transpose(Puzzle, TransposedPuzzle),
    TPuzzle = TransposedPuzzle,
    
    domainConstraint(Puzzle),
    
    allDistinct(Puzzle),
    allDistinct(TPuzzle),
    
    diagonalUnification(Puzzle),
    diagonalUnification(TPuzzle),
    
    headerConstraint(Puzzle),
    headerConstraint(TPuzzle),
    
    groundRow(Puzzle).
    

% ---------------- Requirement 1 ----------------
% domainConstraint(+Puzzle)
% domainConstraintRow(+Row)

% Puzzle is a list of lists and domainConstraint/1 calls domainConstraintRow/1 
% on each row in the puzzle except for the first row.
% domainConstraintRow/1 ensures that all elements in a row
% except the row header is a digit from 1 to 9.

domainConstraint([_|Puzzle]) :- maplist(domainConstraintRow, Puzzle).
domainConstraintRow([_|Row]) :- Row ins 1..9.

% ---------------- Constraint 1 ----------------
% allDistinct(+Puzzle)
% allDistinctRow(+Row)

% allDistinct/1 takes a list of lists as the argument. It calls the 
% allDistinctRow/1 predicate for each row in the puzzle except for 
% the first. allDistinctRow/1 makes sure that all digits in the row
% except the header are distinct.

allDistinct([_|Puzzle]) :- maplist(allDistinctRow, Puzzle).
allDistinctRow([_|Row]) :- all_distinct(Row).

% ---------------- Constraint 2 ----------------
% diagonalUnification(+Puzzle)
% unificationRow(+Puzzle, +RowIndex, ?DiagonalValue)

% diagonalUnification/1 takes a puzzle as an argument. The element
% of the first square on the diagonal line at the top left corner 
% (excluding the ignored square) is the value of all diagonal 
% squares. unificationRow/3 checks that the rest of the diagonal
% elements are equivalent to the first diagonal element. unificationRow/3 takes
% the puzzle without the first two rows, the row index (which is the position 
% the diagonal square should be in each row), and the diagonal value.

diagonalUnification([_,[_, DiagonalValue|_]|Puzzle]) :-
    unificationRow(Puzzle, 2, DiagonalValue).
unificationRow([],_,_).
unificationRow([Row|Puzzle], RowIndex, DiagonalValue) :-
    nth0(RowIndex, Row, Elem),
    Elem #= DiagonalValue,
    RowIndex0 is RowIndex + 1,
    unificationRow(Puzzle, RowIndex0, DiagonalValue).

% ---------------- Contraint 3 ----------------
% headerConstraint(+Puzzle)
% validRowColumn(+Row)
% sumAndProductList(+Row, ?Sum, ?Product)

% Puzzle is a list of lists and headerConstraint/1 calls validRowColumn/1 on 
% each row in the puzzle except the first row. validRowColumn/1 takes a puzzle 
% without the column headers and checks if the given row meets the requirement 
% that the row header is either the sum or the product of all squares in that 
% row with sumAndProductList/3. sumAndProductList/3 takes Row, which is 
% a list of elements. Sum is the sum of elements in Row and Product is the 
% product of elements in Row excluding the row header.

headerConstraint([_|Puzzle]) :- maplist(validRowColumn, Puzzle).

validRowColumn([RowHeader | Row]) :-
    sumAndProductList(Row, Sum, Product),
    (RowHeader #= Sum ;
    RowHeader #= Product).

sumAndProductList([], 0, 1).
sumAndProductList([X|Xs], Sum, Product) :-
    Sum #= Sum0 + X,
    Product #= Product0 * X,
    sumAndProductList(Xs, Sum0, Product0).


% ---------------- Ground ----------------
% groundRow(+Puzzle)

% ground/1 takes a list of lists (representing the puzzle) and uses label/1 
% from the clpdf library to make sure that each variable in each row except 
% for the first row is ground.

groundRow([_| Row]) :- maplist(label, Row).