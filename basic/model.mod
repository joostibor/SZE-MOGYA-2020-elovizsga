param nRows;
set Rows := 1..nRows;
param cashierCount;
param cashierLength;

set ProductGroups;
param space {ProductGroups};

var GroupInRow {ProductGroups, Rows} binary;
var CashierInRow{Rows} binary;
var RowLength {Rows} >= 0;
var LongestRow >= 0;

s.t. OneGroupOneRow {g in ProductGroups}:
    sum{r in Rows} GroupInRow[g, r] = 1;

s.t. NeedPlannedCashier:
    sum{r in Rows} CashierInRow[r] = cashierCount;

s.t. SetRowLength{r in Rows}:
    RowLength[r] = sum{g in ProductGroups} GroupInRow[g, r] * space[g] + CashierInRow[r] * cashierLength;

s.t. SetLongestRow {r in Rows}:
    LongestRow >= RowLength[r];

minimize BuildingLength: LongestRow;

solve;

printf "%f\n",BuildingLength;

end;
