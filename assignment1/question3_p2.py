import z3
import time

# number of deliveries to model
n_stops = 17

Location, (S, A, B, C) = z3.EnumSort('Location', ['S', 'A', 'B', 'C'])

# For each delivery, track where the track has arrived to
truck_location = [z3.Const(f"truck_location_{i}", Location) for i in range(n_stops)]
# travel time from the previous to the current location
travel_time = [z3.Int(f"travel_time_{i}") for i in range(n_stops)]
# how many food packs where delivered in each city
packs_delivered_A = [z3.Int(f"food_delivered_A_{i}") for i in range(n_stops)]
packs_delivered_B = [z3.Int(f"food_delivered_B_{i}") for i in range(n_stops)]
packs_delivered_C = [z3.Int(f"food_delivered_C_{i}") for i in range(n_stops)]
# how many food packs are still on the truck
truck_load = [z3.Int(f"truck_load_{i}") for i in range(n_stops)]

# Running counters for food in each village
food_A = [z3.Int(f"food_A_{i}") for i in range(n_stops)]
food_B = [z3.Int(f"food_B_{i}") for i in range(n_stops)]
food_C = [z3.Int(f"food_C_{i}") for i in range(n_stops)]

# Initial food in each city
initial_food_A = initial_food_B = initial_food_C = 60

# Food capacity in each city
capacity_A = 90
capacity_B = 120
capacity_C = 90

truck_capacity = 150

s = z3.Solver()

# Initial conditions
s.add(truck_load[0] == truck_capacity)
s.add(truck_location[0] == S)
s.add(travel_time[0] == 0)
s.add(packs_delivered_A[0] == 0)
s.add(packs_delivered_B[0] == 0)
s.add(packs_delivered_C[0] == 0)
s.add(food_A[0] == initial_food_A)
s.add(food_B[0] == initial_food_B)
s.add(food_C[0] == initial_food_C)

for i in range(1, n_stops):
    # Compute travel time from the previous location to the one just reached
    loc_from = truck_location[i-1]
    loc_to = truck_location[i]
    s.add(
        z3.If(z3.And(loc_from == S, loc_to == A), travel_time[i] == 15,
              z3.If(z3.And(loc_from == A, loc_to == S), travel_time[i] == 15,
                    z3.If(z3.And(loc_from == S, loc_to == C), travel_time[i] == 15,
                          z3.If(z3.And(loc_from == C, loc_to == S), travel_time[i] == 15,
                                z3.If(z3.And(loc_from == A, loc_to == B), travel_time[i] == 17,
                                      z3.If(z3.And(loc_from == B, loc_to == A), travel_time[i] == 17,
                                            z3.If(z3.And(loc_from == A, loc_to == C), travel_time[i] == 12,
                                                  z3.If(z3.And(loc_from == C, loc_to == A), travel_time[i] == 12,
                                                        z3.If(z3.And(loc_from == B, loc_to == C), travel_time[i] == 13,
                                                              z3.If(z3.And(loc_from == C, loc_to == B), travel_time[i] == 9,
                                                                    False)))))))))))

    # truck can deliver to a village only if it's there
    s.add(
        z3.If(truck_location[i] == A, packs_delivered_A[i] >= 0, packs_delivered_A[i] == 0),
        z3.If(truck_location[i] == B, packs_delivered_B[i] >= 0, packs_delivered_B[i] == 0),
        z3.If(truck_location[i] == C, packs_delivered_C[i] >= 0, packs_delivered_C[i] == 0),
    )

    # deliver food or re-load the truck
    s.add(truck_load[i] >= 0)
    s.add(z3.If(truck_location[i] == S,
                truck_load[i] <= truck_capacity,
                truck_load[i] == truck_load[i-1] - packs_delivered_A[i] - packs_delivered_B[i] - packs_delivered_C[i]))

    # avoid starvation (before the truck reaches the village)
    s.add(
        food_A[i-1] - travel_time[i] > 0,
        food_B[i-1] - travel_time[i] > 0,
        food_C[i-1] - travel_time[i] > 0,
    )

    # compute food in each city at the time of the i-th stop
    s.add(
        food_A[i] == food_A[i-1] - travel_time[i] + packs_delivered_A[i],
        food_B[i] == food_B[i-1] - travel_time[i] + packs_delivered_B[i],
        food_C[i] == food_C[i-1] - travel_time[i] + packs_delivered_C[i],
    )

    # avoid exceeding capacity
    s.add(
        food_A[i] <= capacity_A,
        food_B[i] <= capacity_B,
        food_C[i] <= capacity_C,
      )

# Find the lasso-shaped sequence
k = z3.Int('k') # number of stops before the loop starts
len = z3.Int('len')

s.add(k >= 0, len > 0)
s.add(k + 2*len <= n_stops) # do at least 2 loops

for i in range(n_stops):
    # truck_load[i] == truck[(i - k) % loop_len]
    for j in range(n_stops):
        s.add(
            z3.Implies(
                z3.And(i >= k, j >= k, j == (i - k) % len + k),
                z3.And(
                    truck_load[i] == truck_load[j],
                    truck_location[i] == truck_location[j],
                    food_A[i] == food_A[j],
                    food_B[i] == food_B[j],
                    food_C[i] == food_C[j]
                )
            )
        )

# Run the solver
start_time = time.time()
if s.check() == z3.sat:
    model = s.model()
    print(f"K={model[k]}, L={model[len]}")
    for i in range(n_stops):
        print(model[truck_location[i]], end=", ")
        print(f"Delivery {i}:\n\tLocation = {model[truck_location[i]]}, Time travelled = {model[travel_time[i]]}, Truck load = {model[truck_load[i]]}")
        print(f"\tPacks delivered A={model[packs_delivered_A[i]]}, B={model[packs_delivered_B[i]]}, C={model[packs_delivered_C[i]]},")
        print(f"\tFood left A={model[food_A[i]]}, B={model[food_B[i]]}, C={model[food_C[i]]},")
    print()
else:
    print("No solution found, starvation will eventually occur.")

print(">>> Program runtime is %s seconds" % (time.time() - start_time))