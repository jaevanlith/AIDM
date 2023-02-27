include "globals.mzn";

% Length of schedule
int: w = 7;
% Number of employees
int: groups;
%Number of work shifts
int: numShifts;
% Demand
array[1..numShifts,1..w] of int: demand;
% Max & min length per shift
array[1..numShifts] of int: minShift;
array[1..numShifts] of int: maxShift;
% Min & max length of blocks of assignment: no shift
int: minOff;
int: maxOff;
% Min & max length of blocks of assignment: working shift
int: minOn;
int: maxOn;
% Forbidden sequences of shifts
set of int: shifts = 0..numShifts;
array[1..numShifts] of set of shifts: forbidden;
% Forbidden sequences of shifts of length 3
array[int,1..3] of int: forbidden3;

% Schedule
array[1..groups,1..w] of var 0..numShifts: S;

% == Constraints == %
array[1..numShifts] of int: shifts_array = [j | j in 1..numShifts];

% meet demand; cumulative global constaint?
constraint forall(d in 1..w)(global_cardinality(col(S,d),shifts_array) == col(demand,d));

predicate blockConstraint_min(int: s, int: min) = 
forall (i in 1..groups) (
    forall(j in 1..(w-1) where S[i, j + 1] == s /\ S[i, j] != s) (
          count([S[((j + k) div w) + i,((j + k) mod w) + 1] | k in 0..(min - 1) 
            where ((j + k) div w) + i <= groups], s) >= min
          )
      );
                                              
predicate blockConstraint_max(int: s, int: max) = 
forall (i in 1..groups) (
    forall(j in 1..(w-1) where S[i, j + 1] == s /\ S[i, j] != s) (
          count([S[((j + k) div w) + i,((j + k) mod w) + 1] | k in 0..max
            where ((j + k) div w) + i <= groups], s) < max
          )
      );

% shift blocks
constraint forall (s in shifts_array) (blockConstraint_min(s, minShift[s])); % minima          
constraint forall (s in shifts_array) (blockConstraint_max(s, maxShift[s])); % maxima

% off blocks
constraint blockConstraint_min(0, minOff); % minima     
constraint blockConstraint_max(0, minOn); % minima

% working blocks
constraint forall (i in 1..groups) (
              forall(j in 1..(w-1) where S[i, j + 1] != 0 /\ S[i, j] == 0) (
                    count([S[((j + k) div w) + i,((j + k) mod w) + 1] | k in 0..(minOn - 1) 
                      where ((j + k) div w) + i < groups], S[i, j + 1]) >= minOn
                    )
                ); % minima
                
constraint forall (i in 1..groups) (
              forall(j in 1..(w-1) where S[i, j + 1] != 0 /\ S[i, j] == 0) (
                    count([S[((j + k) div w) + i,((j + k) mod w) + 1] | k in 0..maxOn 
                      where ((j + k) div w) + i <= groups], 0) < maxOn
                    )
                ); % maxima

solve satisfy;