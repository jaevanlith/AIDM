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
set of int: shifts = 1..3;
array[1..3] of set of shifts: forbidden;
% Forbidden sequences of shifts of length 3
% array[??,1..3] of int: forbidden3;

% Schedule
array[1..(groups*w)] of int: T;

% Constraints
