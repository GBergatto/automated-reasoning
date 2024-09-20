import z3

# number of deliveries to model
n_deliveries = 6

Location, (S, A, B, C) = z3.EnumSort('Location', ['S', 'A', 'B', 'C'])

# For each delivery, track where the track has arrived to
truck_location = [z3.Const(f"truck_location_{i}", Location) for i in range(n_deliveries)]
# the current time
delivery_time = [z3.Int(f"time{i}") for i in range(n_deliveries)]
# how much food packs where delivered in each city
packs_delivered_A = [z3.Int(f"food_delivered_{i}") for i in range(n_deliveries)]
packs_delivered_B = [z3.Int(f"food_delivered_{i}") for i in range(n_deliveries)]
packs_delivered_C = [z3.Int(f"food_delivered_{i}") for i in range(n_deliveries)]
# how much food packs are still on the truck
truck_load = [z3.Int(f"truck_load_{i}") for i in range(n_deliveries)]

# Running counters for food in each village
food_A = [z3.Int(f"food_A_{i}") for i in range(n_deliveries)]
food_B = [z3.Int(f"food_B_{i}") for i in range(n_deliveries)]
food_C = [z3.Int(f"food_C_{i}") for i in range(n_deliveries)]

# Initial food in each city
initial_food_A = initial_food_B = initial_food_C = 60

# Food capacity in each city
capacity_A = 90
capacity_B = 120
capacity_C = 90

truck_capacity = 150

s = z3.Solver()

# initial conditions
s.add(truck_load[0] == truck_capacity)
s.add(truck_location[0] == S)
s.add(delivery_time[0] == 0)
s.add(packs_delivered_A[0] == 0)
s.add(packs_delivered_B[0] == 0)
s.add(packs_delivered_C[0] == 0)

# Initial conditions for food counters
s.add(food_A[0] == initial_food_A)
s.add(food_B[0] == initial_food_B)
s.add(food_C[0] == initial_food_C)

for i in range(1, n_deliveries):
    # compute time when the truck reaches its destination
    loc_from = truck_location[i-1]
    loc_to = truck_location[i]
    travel_time = z3.If(z3.And(loc_from == S, loc_to == A), 15,
                        z3.If(z3.And(loc_from == A, loc_to == S), 15,
                              z3.If(z3.And(loc_from == S, loc_to == C), 15,
                                    z3.If(z3.And(loc_from == C, loc_to == S), 15,
                                          z3.If(z3.And(loc_from == A, loc_to == B), 17,
                                                z3.If(z3.And(loc_from == B, loc_to == A), 17,
                                                      z3.If(z3.And(loc_from == A, loc_to == C), 12,
                                                            z3.If(z3.And(loc_from == C, loc_to == A), 12,
                                                                  z3.If(z3.And(loc_from == B, loc_to == C), 13,
                                                                        z3.If(z3.And(loc_from == C, loc_to == B), 9,
                                                                              -1))))))))))

    s.add(travel_time > 0) # avoid unreachable destinations
    s.add(delivery_time[i] == delivery_time[i-1] + travel_time)

    # truck can deliver to a village only if it's there
    s.add(z3.If(truck_location[i] == A, packs_delivered_A[i] >= 0, packs_delivered_A[i] == 0))
    s.add(z3.If(truck_location[i] == B, packs_delivered_B[i] >= 0, packs_delivered_B[i] == 0))
    s.add(z3.If(truck_location[i] == C, packs_delivered_C[i] >= 0, packs_delivered_C[i] == 0))

    # deliver food or re-load the truck
    s.add(truck_load[i] >= 0)
    s.add(z3.If(truck_location[i] == S,
                truck_load[i] == truck_capacity,
                truck_load[i] == truck_load[i-1] - packs_delivered_A[i] - packs_delivered_B[i] - packs_delivered_C[i]))

    # compute food in each city at the time of the i-th stop
    s.add(food_A[i] == food_A[i-1] - travel_time + packs_delivered_A[i])
    s.add(food_B[i] == food_B[i-1] - travel_time + packs_delivered_B[i])
    s.add(food_C[i] == food_C[i-1] - travel_time + packs_delivered_C[i])

    # avoid starvation
    s.add(food_A[i] > 0)
    s.add(food_B[i] > 0)
    s.add(food_C[i] > 0)

    # avoid exceeding capacity
    s.add(food_A[i] <= capacity_A)
    s.add(food_B[i] <= capacity_B)
    s.add(food_C[i] <= capacity_C)

# Run the solver
if s.check() == z3.sat:
    model = s.model()
    for i in range(n_deliveries):
        print(f"Delivery {i}:\n\tLocation = {model[truck_location[i]]}, Time = {model[delivery_time[i]]}, Truck load = {model[truck_load[i]]}")
        print(f"\tPacks delivered A={model[packs_delivered_A[i]]}, B={model[packs_delivered_B[i]]}, C={model[packs_delivered_C[i]]},")
        print(f"\tFood left A={model[food_A[i]]}, B={model[food_B[i]]}, C={model[food_C[i]]},")
else:
    print("No solution found, starvation will eventually occur.")
