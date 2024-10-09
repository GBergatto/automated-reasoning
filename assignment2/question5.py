from buddy import BuDDy
#Question 5: Permissive Configuration
chosen_file = "toybox.dimacs" #Decide on the config file

#Build the variables
with open(f"conf-dimacs/{chosen_file}", "r") as f:
    config_start = f.readline() #Config Start
    config_start = config_start.strip().split()

    comment_order = f.readline() #Read Variable Order from file
    variable_order = comment_order.strip().split()[2:]
    var_order = [f"x_{i}" for i in variable_order]
    manager = BuDDy(var_order, "buddy.windows")
    variables = manager.var_bdds
    config_BDD = manager.true #The whole config BDD
    for line in f:
        line_split = line.strip().split()
        if line_split[0]!= "c": #Extract clauses in file
            clause_BDD = manager.false #Clause construct
            for line_literal in line_split:
                if line_literal != "0":
                    if line_literal[0] != "-":
                        clause_BDD = manager.apply("or",variables[f"x_{line_literal}"],clause_BDD)
                    else:
                        clause_BDD = manager.apply("or",manager.apply("~",variables[f"x_{line_literal[1:]}"]),clause_BDD)
            config_BDD = manager.apply("and",config_BDD,clause_BDD)
    print(f"The total number of valid configurations for {chosen_file} is {manager.satcount(config_BDD)}")
        