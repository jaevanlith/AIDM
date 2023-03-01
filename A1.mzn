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

% Constraints
array[1..numShifts] of int: shifts_array = [j | j in 1..numShifts];
constraint forall(d in 1..w)(global_cardinality(col(S,d),shifts_array) == col(demand,d));

% Forbidden sequences of length 2 constraint
constraint forall(g in 1..groups)(
              forall(d in 1..(w-1))(not (S[g,d+1] in forbidden[S[g,d]])) 
              /\ 
              not (S[g,1] in forbidden[S[g,w]]));

% Forbidden sequences of length 3 constraint
constraint forall(r in 1..(length(forbidden3) div 3))(
              forall(g in 1..groups)(
                  forall(d in 1..(w-2))(forbidden3[r,1] != S[g,d] \/ forbidden3[r,2] != S[g,d+1] \/ forbidden3[r,3] != S[g,d+2])
                  /\
                  (forbidden3[r,1] != S[g,(w-1)] \/ forbidden3[r,2] != S[g,w] \/ forbidden3[r,3] != S[g,1])
                  /\
                  (forbidden3[r,1] != S[g,(w)] \/ forbidden3[r,2] != S[g,1] \/ forbidden3[r,3] != S[g,2])));

solve satisfy;