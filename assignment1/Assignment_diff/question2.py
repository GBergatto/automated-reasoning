from z3 import *
# Print SAT
def print_sat(model,Widths,Heights,X_LLCs,Y_LLCs):
    print("SAT condition found:")
    for i in range(11):
        print(f"Poster {i+1}: Width = {model.eval(Widths[i])} Height = {model.eval(Heights[i])} X-Coordinate of LLC = {model.eval(X_LLCs[i])} Y-Coordinate of LLC = {model.eval(Y_LLCs[i])}", end="")
        print(f" [{model.eval(Widths[i])},{model.eval(Heights[i])},{model.eval(X_LLCs[i])},{model.eval(Y_LLCs[i])}]", end="")
        print()
#Define solver
SAT_Solver = Solver()
#Define poster size constraints
Posters = [[4,5],[4,6],[5,21],
           [6,9],[6,8],[6,10],
           [6,11],[7,12],[8,9],
           [10,11],[10,20]
           ]
layout_width, layout_height = 30, 30

Posters_Width = Array("w",IntSort(),IntSort()) # Width of rectangles
Posters_Height = Array("h",IntSort(),IntSort()) # Height of rectangles
Poster_X_LLCs = Array("x",IntSort(),IntSort()) # x-coord of left lower corners
Poster_Y_LLCs = Array("y",IntSort(),IntSort()) # y-coord of left lower corners

# The constraints for each poster
for poster_idx in range(len(Posters)):
    SAT_Solver.add(
        Or( # Poster size(width and height) constraints
            And(Posters_Width[poster_idx]==Posters[poster_idx][0],Posters_Height[poster_idx]==Posters[poster_idx][1]),
            And(Posters_Width[poster_idx]==Posters[poster_idx][1],Posters_Height[poster_idx]==Posters[poster_idx][0])
        ),
        And( # Fit the posters into the large sheet canvas (Fit Constraints)
            And(Poster_X_LLCs[poster_idx] >= 0, Poster_X_LLCs[poster_idx]+Posters_Width[poster_idx] <= layout_width), # Width Fit
            And(Poster_Y_LLCs[poster_idx] >= 0, Poster_Y_LLCs[poster_idx]+Posters_Height[poster_idx] <= layout_height) # Height Fit
        )    
    )

# Overlap Constraints
for i_poster_idx in range(len(Posters)):
    for j_poster_idx in range(i_poster_idx+1,len(Posters)):
        SAT_Solver.add(
            Or(
                Poster_X_LLCs[i_poster_idx]+Posters_Width[i_poster_idx] <= Poster_X_LLCs[j_poster_idx],
                Poster_X_LLCs[j_poster_idx]+Posters_Width[j_poster_idx] <= Poster_X_LLCs[i_poster_idx],
                Poster_Y_LLCs[i_poster_idx]+Posters_Height[i_poster_idx] <= Poster_Y_LLCs[j_poster_idx],
                Poster_Y_LLCs[j_poster_idx]+Posters_Height[j_poster_idx] <= Poster_Y_LLCs[i_poster_idx]
            )
        )

#Constraints for section 2.1
line_2_1_val, line_2_1_axis= Int("value1"),Int("axis1")
SAT_Solver.add(0 < line_2_1_val, line_2_1_val < layout_width)

x_coord_constraints_2_1, y_coord_constraints_2_1 = True, True 
for poster_idx in range(len(Posters)):
    x_coord_constraints_2_1 = And(x_coord_constraints_2_1,Not(And(Poster_X_LLCs[poster_idx] < line_2_1_val, line_2_1_val < Poster_X_LLCs[poster_idx]+Posters_Width[poster_idx])))
    y_coord_constraints_2_1 = And(y_coord_constraints_2_1,Not(And(Poster_Y_LLCs[poster_idx] < line_2_1_val, line_2_1_val < Poster_Y_LLCs[poster_idx]+Posters_Height[poster_idx])))

SAT_Solver.add(
    Or(And(x_coord_constraints_2_1,line_2_1_axis==0),And(y_coord_constraints_2_1,line_2_1_axis==1))
)

print("<--Section2.1-->")
result = SAT_Solver.check()
if result == sat:
    sat_model = SAT_Solver.model()
    print_sat(sat_model,Posters_Width,Posters_Height,Poster_X_LLCs,Poster_Y_LLCs)
    print(f"The value of line is {sat_model.eval(line_2_1_val)} and axis is {"x" if sat_model.eval(line_2_1_axis) == 0 else "y"}")
else:
    print("UNSAT")
print("<--Section2.1-->")

#Constraints for section 2.2
SAT_Solver.push()
SAT_Solver.add(
    10 <= line_2_1_val,
    line_2_1_val <= layout_width - 10
)


print("<--Section2.2-->")
result = SAT_Solver.check()
if result == sat:
    sat_model = SAT_Solver.model()
    print_sat(sat_model,Posters_Width,Posters_Height,Poster_X_LLCs,Poster_Y_LLCs)
    print(f"The value of line is {sat_model.eval(line_2_1_val)} and axis is {"x" if sat_model.eval(line_2_1_axis) == 0 else "y"}")
else:
    print("UNSAT")
SAT_Solver.pop()
print("<--Section2.2-->")

#Constraints for section 2.3
line_2_3_val, line_2_3_axis = Int("value2"),Int("axis2")
SAT_Solver.add(0 < line_2_3_val, line_2_3_val < layout_width)

print("<--Section2.3-->")
x_coord_constraints_2_3, y_coord_constraints_2_3 = True, True 
for poster_idx in range(len(Posters)):
    x_coord_constraints_2_3 = And(x_coord_constraints_2_3,Not(And(Poster_X_LLCs[poster_idx] < line_2_3_val, line_2_3_val < Poster_X_LLCs[poster_idx]+Posters_Width[poster_idx])))
    y_coord_constraints_2_3 = And(y_coord_constraints_2_3,Not(And(Poster_Y_LLCs[poster_idx] < line_2_3_val, line_2_3_val < Poster_Y_LLCs[poster_idx]+Posters_Height[poster_idx])))

SAT_Solver.add(
    Or(And(x_coord_constraints_2_1,y_coord_constraints_2_3),And(y_coord_constraints_2_1,x_coord_constraints_2_3))
)

result = SAT_Solver.check()
if result == sat:
    sat_model = SAT_Solver.model()
    print_sat(sat_model,Posters_Width,Posters_Height,Poster_X_LLCs,Poster_Y_LLCs)
    print(f"The value of line is {sat_model.eval(line_2_1_val)} and axis is {"x" if sat_model.eval(line_2_1_axis) == 0 else "y"}")
    print(f"The value of line is {sat_model.eval(line_2_3_val)} and axis is {"x" if sat_model.eval(line_2_3_axis) == 0 else "y"}")
else:
    print("UNSAT")
print("<--Section2.3-->")
