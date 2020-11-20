param nRows;
set Rows := 1..nRows;

param cashierCount;
set Cashiers := 1..cashierCount;
param cashierLength;
param maxRowLength;

set ProductGroups;
param space {ProductGroups} >= 0;
param averagePrice {ProductGroups} >= 0;

set MustBeTogether within {ProductGroups, ProductGroups};
set MustBeSeparated within {ProductGroups, ProductGroups};

set CustomerGroups;
param count {CustomerGroups} >= 0;
param probabilityToBuy {CustomerGroups} >= 0;
param buys {CustomerGroups, ProductGroups} binary;

param M := 1000;

var GroupInRow {ProductGroups, Rows} binary;
var RowsWithCashier{Rows, Cashiers} binary;
var CashierInRow{Rows} binary;
var RowLength {Rows} >= 0;
var PlusIncome {CustomerGroups, Rows} >= 0;
var GoToRow {CustomerGroups, Rows} binary;

s.t. IsRowHasCashier {c in Cashiers, r in Rows}:
    CashierInRow[r] >= RowsWithCashier[r,c]; 

s.t. EveryCashierCanPlaced {c in Cashiers}:
    sum{r in Rows} RowsWithCashier[r,c] = 1;

s.t. SetRowLength{r in Rows}:
    RowLength[r] = sum{g in ProductGroups} GroupInRow[g, r] * space[g] + sum{c in Cashiers}RowsWithCashier[r,c] * cashierLength;

s.t. RowLengthCantBeTooLong {r in Rows}:
    RowLength[r] <= maxRowLength;

s.t. OneGroupOneRow {g in ProductGroups}:
    sum{r in Rows} GroupInRow[g, r] = 1;

s.t. TogetherGroupsGoOneRow {(g1, g2) in MustBeTogether, r in Rows}:
    GroupInRow[g1, r] = GroupInRow[g2, r];

s.t. SeparatedGroupsCantGoOneRow {(g1, g2) in MustBeSeparated, r in Rows}:
    GroupInRow[g1, r] <= 1 - GroupInRow[g2, r];

s.t. RowHasInterestProduct {r in Rows, g in ProductGroups, c in CustomerGroups}:
    GoToRow[c, r] >= buys[c,g] * GroupInRow[g,r];

s.t. BuyWithProability1 {c in CustomerGroups, r in Rows}:
    PlusIncome[c,r] <= sum{g in ProductGroups: buys[c,g] = 0} GroupInRow[g,r]*averagePrice[g]*probabilityToBuy[c] + M*(1-GoToRow[c,r]);

s.t. BuyWithProability2 {c in CustomerGroups, r in Rows}:
    PlusIncome[c,r] >= sum{g in ProductGroups: buys[c,g] = 0} GroupInRow[g,r]*averagePrice[g]*probabilityToBuy[c] - M*(1-GoToRow[c,r]);

s.t. IfRowHasCashierDoesntMatter1{c in CustomerGroups, r in Rows}:
    PlusIncome[c,r] <= 0 + M*(1-CashierInRow[r]);

s.t. IfRowHasCashierDoesntMatter2{c in CustomerGroups, r in Rows}:
    PlusIncome[c,r] >= 0 - M*(1-CashierInRow[r]);

maximize ManipulateIncome:
    sum{c in CustomerGroups, r in Rows} PlusIncome[c,r] * count[c];

solve;

printf "%f\n",ManipulateIncome;

end;
