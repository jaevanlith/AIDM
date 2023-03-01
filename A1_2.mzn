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

array[1..(groups * w)] of var 0..numShifts: T;
var 0..(w-1): o; % offset

% == Constraints == %
array[1..numShifts] of int: shifts_array = [j | j in 1..numShifts];

% meet demand; cumulative global constaint?
constraint forall(d in 1..w)(global_cardinality([T[(d + o + w * i - 1) mod (groups * w) + 1] | i in 0..(groups - 1)], shifts_array) == col(demand, d));
constraint forall(d in 1..w)(count([T[(d + o + w * i - 1) mod (groups * w) + 1] | i in 0..(groups - 1)], 0) == groups - sum(col(demand,d))); % optimization: redundant constraint

% predicate blockConstraint_min(int: s, int: min) = forall(i in 2..(groups * w) where T[i] == s /\ T[i - 1] != s) 
%                                                      (count([T[j + i] | j in 0..(min - 1) 
%                                                             where j + i <= groups * w], s) == min
%                                                       );
                                                      
predicate blockConstraint_min(int: s, int: min) = forall(i in 2..(groups * w) where T[i] == s /\ T[i - 1] != s) % optimization
                                                     (((min - 1) + i <= groups * w) /\ all_equal([T[j + i] | j in 0..(min - 1)]));

predicate blockConstraint_max(int: s, int: min, int: max) = (forall(i in 2..(groups * w) where T[i] == s /\ T[i - 1] != s) 
                                                                (count([T[j + i] | j in min..max 
                                                                      where j + i <= groups * w], s) <= max - min
                                                            ));

% shift blocks
constraint forall (s in shifts_array) (blockConstraint_min(s, minShift[s])); % minima          
constraint forall (s in shifts_array) (blockConstraint_max(s, minShift[s], maxShift[s])); % maxima

% off blocks
constraint blockConstraint_min(0, minOff); % minima     
constraint blockConstraint_max(0, minOff, maxOff); % maxima

% working blocks
constraint forall(i in 2..(groups * w) where T[i] != 0 /\ T[i - 1] == 0) 
           (among([T[j + i] | j in 0..(minOn - 1) 
                  where j + i <= groups * w], 1..numShifts) == minOn
            ); % minima
constraint forall(i in 2..(groups * w) where T[i] != 0 /\ T[i - 1] == 0) 
            (among([T[j + i] | j in minOn..maxOn 
                  where j + i <= groups * w], 1..numShifts) <= maxOn - minOn
            ); % maxima
            
% consider first element
constraint (count([T[j + 1] | j in 0..(minOff - 1) where j + 1 <= groups * w], 0) == minOff);
constraint (count([T[j + 1] | j in minOff..maxOff where j + 1 <= groups * w], 0) <= maxOff - minOff);

% symmetry breaking (cyclic nature)             
constraint T[1] = 0;
constraint T[groups * w] != 0; % block contraints assume that the last and first elements are not equal!!

% forbidden sequences
predicate equalArray3(array[1..3] of int: arr1, array[1..3] of var int: arr2) = forall (k in 1..3) (arr1[k] == arr2[k]);

constraint forall(i in 1..(groups * w) where T[i] != 0) (not member(forbidden[T[i]], T[(i) mod (groups * w) + 1]));
constraint forall(i in 1..(groups * w) where T[i] != 0) (forall(j in 1..(length(forbidden3) div 3)) ( not
                equalArray3 (row(forbidden3, j), [T[(i + k - 1) mod (groups * w) + 1] | k in 0..2])));

% symmetry breaking (offset)
constraint o == min([(if sum(col(demand,d)) > sum(col(demand,(d mod w + 1))) then d else w+1 endif) | d in 1..w]) - 1;

% maximize free weekends
var int : sat = (5 + o) mod (w);
var int : sun = (6 + o) mod (w);
var int : f = count([T[sat + i * w] | i in 0..(groups - 1)], 0) + count([T[sun + i * w] | i in 0..(groups - 1)], 0);

% free weekend distance
array[int] of var int : f_full = [T[sat + i * w] + T[sun + i * w] | i in 0..(groups - 1)];
array[int] of var opt int : dist1 = [(j - 1) * (j - 1) | i, j in 1..groups where (f_full[(i + j - 1) mod (groups) + 1] = 0 /\ f_full[i] = 0)];
array[int] of var opt int : dist2 = [groups * groups | i in 1..groups where f_full[i] != 0];

solve maximize f - sum(dist1) - sum(dist2);