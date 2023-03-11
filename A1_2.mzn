include "globals.mzn";

% == INPUT VARIABLES == %
% Length of schedule
int: w = 7;
% Number of employees
int: groups;
% Number of work shifts
int: numShifts;
% Demand
array[1..numShifts,1..w] of int: demand;
% Min & max length per shift
array[1..numShifts] of int: minShift;
array[1..numShifts] of int: maxShift;
% Min & max length of blocks of days off
int: minOff;
int: maxOff;
% Min & max length of blocks of working days
int: minOn;
int: maxOn;
% Forbidden sequences of shifts
set of int: shifts = 0..numShifts;
array[1..numShifts] of set of shifts: forbidden;
% Forbidden sequences of shifts of length 3
array[int,1..3] of int: forbidden3;
% Array containing the possible shifts
array[1..numShifts] of int: shifts_array = [j | j in 1..numShifts];

% == DECISION VARIABLES == %
% Cyclic schedule in list form
array[1..(groups * w)] of var 0..numShifts: T;
% Offset (shifts to the right)
var 0..(w-1): o;

% == CONSTRAINTS == %
% Meet demand
% For each day and each shift, the number of assigned employees should match the demand
% Inference annotation: use domain-consistency propagator
constraint forall(d in 1..w)(global_cardinality([T[(d + o + w * i - 1) mod (groups * w) + 1] | i in 0..(groups - 1)], shifts_array) == col(demand, d)) :: domain;
% For each day and each shift, the number of free employees should match the total number of employees minus the assigned employees
constraint forall(d in 1..w)(count([T[(d + o + w * i - 1) mod (groups * w) + 1] | i in 0..(groups - 1)], 0) == groups - sum(col(demand,d))); % optimization: redundant constraint

% Predicates to constrain the block size
% For each day in which a new block starts (=different shift as its predecessor)...
% ...all the consecutive days within the minimal range should have the same shift                                            
predicate blockConstraint_min(int: s, int: min) = forall(i in 2..(groups * w) where T[i] == s /\ T[i - 1] != s) % optimization
                                                     (((min - 1) + i <= groups * w) /\ all_equal([T[j + i] | j in 0..(min - 1)]));
% ...there should be 1 or more different shifts in the days ranging from the minimum and maximum block length
predicate blockConstraint_max(int: s, int: min, int: max) = (forall(i in 2..(groups * w) where T[i] == s /\ T[i - 1] != s) 
                                                                (count([T[j + i] | j in min..max 
                                                                      where j + i <= groups * w], s) <= max - min
                                                            )); 

% Shift blocks
constraint forall (s in shifts_array) (blockConstraint_min(s, minShift[s])); % minima          
constraint forall (s in shifts_array) (blockConstraint_max(s, minShift[s], maxShift[s])); % maxima

% Day off blocks
constraint blockConstraint_min(0, minOff); % minima     
constraint blockConstraint_max(0, minOff, maxOff); % maxima
% Consider first element (only necessary for day off blocks, because of symmetry breaking)
constraint (count([T[j + 1] | j in 0..(minOff - 1) where j + 1 <= groups * w], 0) == minOff);
constraint (count([T[j + 1] | j in minOff..maxOff where j + 1 <= groups * w], 0) <= maxOff - minOff);

% Working day blocks
% For each working day after a day off...
% ...all the consecutive days within the minimal range should be working days
constraint forall(i in 2..(groups * w) where T[i] != 0 /\ T[i - 1] == 0) 
           (among([T[j + i] | j in 0..(minOn - 1) 
                  where j + i <= groups * w], 1..numShifts) == minOn
            ); % minima
% ...there should be 1 or more days off in the days ranging from the minimum and maximum block length
constraint forall(i in 2..(groups * w) where T[i] != 0 /\ T[i - 1] == 0) 
            (among([T[j + i] | j in minOn..maxOn 
                  where j + i <= groups * w], 1..numShifts) <= maxOn - minOn
            ); % maxima

% Symmetry breaking (cyclic nature)
% First day is a day off           
constraint T[1] = 0;
% Last day is a working day
constraint T[groups * w] != 0; 
% As a consequence: block contraints assume that the last and first elements are not equal (so T(groups*w) and T(1) can never be in the same block)

% Forbidden sequences
% Compare two arrays of length 3
predicate equalArray3(array[1..3] of int: arr1, array[1..3] of var int: arr2) = forall (k in 1..3) (arr1[k] == arr2[k]);
% For each working day, the next day should not have a forbidden shift assigned to it
constraint forall(i in 1..(groups * w) where T[i] != 0) (not member(forbidden[T[i]], T[(i) mod (groups * w) + 1]));
% For each working day, the next two days should not form a forbidden sequence
constraint forall(i in 1..(groups * w) where T[i] != 0) (forall(j in 1..(length(forbidden3) div 3)) ( not
                equalArray3 (row(forbidden3, j), [T[(i + k - 1) mod (groups * w) + 1] | k in 0..2])));

% Symmetry breaking (offset)
% Two cases:
% 1. If each day has a constant demand, then it does not matter what the offset is
% 2. If any day has a higher total demand than the previous day, then one or more working blocks should start on that day and offset can be fixed
constraint member(2..maxOff, o) \/ o == (w - (max([d | d in 1..w where sum(col(demand, d mod (w) + 1)) < sum(col(demand, d))]) - 1)) mod w;

% Maximize free weekends
% Define the indexes of Saturday and Sunday given the offset
var int : sat = (5 + o) mod (w) + 1;
var int : sun = (6 + o) mod (w) + 1;
% Define an array of weekends where 0 is a free weekend
array[int] of var int : f_full = [T[sat + i * w] + T[sun + i * w] | i in 0..(groups - 1)];

% Distribution of free weekends (not used in solving)
% Define an array of the distance to the next free weekend, the maximum value is assigned to non-free weekends
array[int] of var opt int : dist = 
  [if f_full[i] = 0 
   then min([(j - 1) * (j - 1) | j in 1..groups where f_full[(i + j - 1) mod groups + 1] = 0]) 
   else groups * groups
   endif | i in 1..groups];

% == OBJECTIVE == %
solve 
  % Try free weekend days first
%   :: int_search([T[sun + i * w] | i in 0..(groups - 1)], first_fail, indomain_min) 
%   :: int_search([T[sat + i * w] | i in 0..(groups - 1)], first_fail, indomain_min)
%   :: int_search([o], first_fail, indomain) 
  % Maximize the sum of free weekends (based on free weekend array)
  maximize sum([1 | i in 1..groups where f_full[i] == 0]);

% == OUTPUT == % 
output [
% Show the final schedule (corrected for the offset)
"[", concat([(if fix(T[(i + o - 1) mod (groups * w) + 1]) == 0 then "-," else concat([show(T[(i + o - 1) mod (groups * w) + 1]), ","]) endif) | i in 1..(groups * w - 1)] ++ [(if fix(T[(i + o - 1) mod (groups * w) + 1]) == 0 then "-" else concat([show(T[(i + o - 1) mod (groups * w) + 1])]) endif) | i in (groups * w)..(groups * w)]), "]\n",

% Show the number of free weekends
show(sum([1 | i in 1..groups where f_full[i] == 0]))]