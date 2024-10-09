import angr, claripy
# Load the binary
project = angr.Project('./test.o', auto_load_libs=False)

# Define the address of the firstCall function
firstCall_addr = project.loader.main_object.get_symbol("firstCall")

# Define the address of the helloWorld function
helloWorld_addr = project.loader.main_object.get_symbol("helloWorld")
# Create a symbolic variable for the firstCall arg
input_arg = claripy.BVS('input_arg', 32)
input_arg2 = claripy.BVS('input_arg2', 32)

# Create a blank state at the address of the firstCall function
init_state = project.factory.blank_state(addr=firstCall_addr.rebased_addr)

# Assuming the calling convention passes the argument in a register
# (e.g., x86 uses edi for the argument)
init_state.regs.edi = input_arg
init_state.regs.esi = input_arg2
# Create a simulation manager
simgr = project.factory.simulation_manager(init_state)

# Explore the binary, looking for the address of helloWorld
simgr.explore(find=helloWorld_addr.rebased_addr)

# Check if we found a state that reached the target
if simgr.found:
    input_value = simgr.found[0].solver.eval(input_arg)
    print(f"Value of input_arg that reaches HelloWorld: {input_value}")
    print(simgr.found[0].solver.eval(input_arg2))
    # Get the constraints for reaching the helloWorld function
    constraints = simgr.found[0].solver.constraints
    # Create a solver with the constraints
    solver = claripy.Solver()
    solver.add(constraints)
    min_val = solver.min(input_arg)
    max_val = solver.max(input_arg)
    print(f"Function arg: min = {min_val}, max = {max_val}")
    print("Argument 2")
    min_val = solver.min(input_arg2)
    max_val = solver.max(input_arg2)
    print(f"Function arg: min = {min_val}, max = {max_val}")
else:
    print("Did not find a state that reaches HelloWorld.")
