import z3


def print_solution(model):
    print(f"Max number of dopples pallets: {model.evaluate(objective)}")
    
    for i in range(num_trucks):
        nuzzles_count = model[nuzzles[i]].as_long()
        prittles_count = model[prittles[i]].as_long()
        skipples_count = model[skipples[i]].as_long()
        crottles_count = model[crottles[i]].as_long()
        dupples_count = model[dupples[i]].as_long()
        
        # Compute the total weight for truck i
        tw = (
            nuzzles_count * nuzzles_weight +
            prittles_count * prittles_weight +
            skipples_count * skipples_weight +
            crottles_count * crottles_weight +
            dupples_count * dupples_weight
        )
        
        print(f"Truck {i+1}:")
        print(f"  Nuzzles: {model[nuzzles[i]]}")
        print(f"  Prittles: {model[prittles[i]]}")
        print(f"  Skipples: {model[skipples[i]]}")
        print(f"  Crottles: {model[crottles[i]]}")
        print(f"  Dupples: {model[dupples[i]]}")
        print(f"Total weight: {tw} kg")


# Trucks
num_trucks = 6
max_weight = 8000
max_pallets = 10

# Pallets
nuzzles_weight = 800
nuzzles_total = 6

prittles_weight = 405
prittles_total = 12

skipples_weight = 500
skipples_total = 15

crottles_weight = 2500
crottles_total = 8

dupples_weight = 600

solver = z3.Optimize()

### Variables ###
nuzzles = [z3.Int(f'nuzzles_t{i}') for i in range(num_trucks)]
prittles = [z3.Int(f'prittles_t{i}') for i in range(num_trucks)]
skipples = [z3.Int(f'skipples_t{i}') for i in range(num_trucks)]
crottles = [z3.Int(f'crottles_t{i}') for i in range(num_trucks)]
dupples = [z3.Int(f'dupples_t{i}') for i in range(num_trucks)]

### Constraints ###
# all trucks must contain a non-negative number of pallets
for i in range(num_trucks):
    solver.add(nuzzles[i] >= 0, prittles[i] >= 0, skipples[i] >= 0, crottles[i] >= 0, dupples[i] >= 0)

# total pallets of each type must match the required number
solver.add(z3.Sum(nuzzles) == nuzzles_total)
solver.add(z3.Sum(prittles) == prittles_total)
solver.add(z3.Sum(skipples) == skipples_total)
solver.add(z3.Sum(crottles) == crottles_total)

# only two trucks can carry skipples
solver.add(z3.Sum([z3.If(skipples[i] > 0, 1, 0) for i in range(num_trucks)]) <= 2)

# prittles must be distributed over at least 5 trucks
solver.add(z3.Sum([z3.If(prittles[i] > 0, 1, 0) for i in range(num_trucks)]) >= 5)

# max 10 pallets per truck and capacity
for i in range(num_trucks):
    total_weight = z3.Sum(
        nuzzles[i] * nuzzles_weight,
        prittles[i] * prittles_weight,
        skipples[i] * skipples_weight,
        crottles[i] * crottles_weight,
        dupples[i] * dupples_weight
    )
    num_pallets = nuzzles[i] + prittles[i] + skipples[i] + crottles[i] + dupples[i]

    solver.add(total_weight <= max_weight)
    solver.add(num_pallets <= max_pallets)

### Solution 1.1
objective = z3.Sum(dupples)

solver.maximize(objective)
print("--- Part 1 ---")
if solver.check() == z3.sat:
    model = solver.model()
    print_solution(model)
else:
    print("No solution found.")

# Solution 1.2
for i in range(num_trucks):
    solver.add(z3.If(crottles[i] > 0, dupples[i]>=2, True))

print("\n--- Part 2 ---")
solver.maximize(objective)
if solver.check() == z3.sat:
    model = solver.model()
    print_solution(model)
else:
    print("No solution found.")

