#-----------------SYM-------------------#

from EtherCost import tools
import networkx as nx
import matplotlib.pyplot as plt
from networkx.drawing.nx_agraph import write_dot
import _pickle as pickle
import json

target = [] #source file split by lines
translation = [] #list of program opcodes replaced by Souper IR opcodes
var_dict = {} #Dict of each var's opcode
stack_counts = tools.stack_counts
global_dependants = []
ssa_op_dict = {} #To be operated on indentically to regular stack, but will hold opcodes instead of vars and values
global_state = [[0,0,[],[],[]]] #i, block number, stack, destination, call history
g = nx.DiGraph()
jumpi_dest_lst = []
jump_dest_lst = []
block_total = 0

def resolve_jump_dests(source_file):
    jump_map = {}
    push_offset = 0
    block = 0
    block_map = {}
    opcode_block = {}
    block_op_list = []
    global block_total
    with open(source_file, "r") as f:
        ops = f.read().splitlines()
        for i, each in enumerate(ops):
            if "PUSH" in each:
                push_op = each.split()[0]
                try:
                    push_offset += int(push_op[-2:])
                except:
                    push_offset += int(push_op[-1:])
            if each == "JUMPDEST":
                jump_map[i+push_offset]=i

        for i, each in enumerate(ops):
            if each == "JUMPDEST":
                opcode_block[block]=block_op_list
                block+=1
                block_op_list = []
            if block > block_total:
                block_total = block
            block_map[i]=block
            block_op_list.append(each)

        opcode_block[block_total]=block_op_list

    with open("opcode_block_map_"+source_file+".pickle", "wb") as f:
        pickle.dump(opcode_block, f, protocol=2)

    return jump_map, block_map

def format_source(source_file):
    with open(source_file, "r") as f:
        target = f.read().splitlines()

    for i, opcode in enumerate(target):
        if "PUSH" in opcode:
            if "0x" not in opcode:
                try:
                    push_op = opcode+" "+target[i+1]
                    translation.append(push_op)
                except IndexError:
                    print("Error Formatting PUSH instruction at: ",i)
            else:
                translation.append(opcode)
        else:
            if "0x" not in opcode:
                translation.append(opcode)

    foutname = "translation_"+source_file
    with open(foutname, "w") as f:
        for each in translation:
            f.write("%s\n" % each)


def _clean_opcode(opcode):
    if "PUSH" in opcode:
        return "PUSH"
    elif "DUP" in opcode:
        return "DUP"
    elif "SWAP" in opcode:
        return "SWAP"
    else:
        return opcode

def get_dependencies_long(i, opcode, target):
    dependants = [[opcode]]
    c = i-1
    if stack_counts[opcode][0] > 0:
        inputs_no = stack_counts[opcode][0]
        while  inputs_no > 0:
            dependants[0].extend([target[c]])
            diff = (stack_counts[_clean_opcode(target[c])][1]) - (stack_counts[_clean_opcode(target[c])][0])
            inputs_no -= diff
            c -= 1
            #conditions added to stop at jump, this gives in-block dependancies
            if target[c] == "JUMP" or "JUMPI":
                dependants[0].extend([target[c]])
                break

    return dependants 

def _stack_pop(opcode, stack):
    for x in range(0, stack_counts[opcode][0]):
                del stack[0]
    return stack

def sym_ex(source_file, c=0, r_stack=[], r_var_count=0, r_call_history=[], r_j_prev=False):
    dest = 0
    stack = r_stack
    var_count = r_var_count
    call_history = r_call_history
    j_prev = r_j_prev

    with open(source_file, "r") as f:
        target = f.read().splitlines()
    hfs_op_map, block_map = resolve_jump_dests(source_file)
    i = c
    block_c = 0
    while i < len(target):

        var_increment = False #switch to control incrementation of var names in SSA

#----------------------Stack related Opcodes----------------------#
        if "PUSH" in target[i]:
            stack.insert(0,(int(target[i].split(" ")[1], 16)))
            j_prev = False

        elif "DUP" in target[i]:
            try:
                stack_pos = int(target[i][-2:])
            except:
                pass
            try:
                stack_pos = int(target[i][-1:])
            except:
                pass
            global_dependants.extend(get_dependencies_long(i, _clean_opcode(target[i]), target))
            stack.insert(0,stack[stack_pos-1])
            j_prev = False

        elif "SWAP" in target[i]:
            stack_pos = 0
            try:
                stack_pos = int(target[i][-2:])
            except:
                pass
            try:
                stack_pos = int(target[i][-1:])
            except:
                pass
            global_dependants.extend(get_dependencies_long(i, _clean_opcode(target[i]), target))
            temp = stack[0]
            stack[0] = stack[stack_pos]
            stack[stack_pos] = temp
            j_prev = False

        elif target[i] == "POP":
            stack = _stack_pop(target[i], stack)
            j_prev = False
#---------------------------Mathematical & logical Opcodes------------------------------------------#

        elif target[i] == "EXP":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            stack = _stack_pop(target[i], stack)          
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "AND":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")


            stack = _stack_pop(target[i], stack)          
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "XOR":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "SUB":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "SDIV":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            ssa_op_dict[var_name] = i+1
            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "SLT":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            ssa_op_dict[var_name] = i+1
            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "ADD":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            ssa_op_dict[var_name] = i+1
            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "MUL":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            ssa_op_dict[var_name] = i+1
            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "EQ":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            ssa_op_dict[var_name] = i+1
            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "OR":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "NOT":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False
        
        elif target[i] == "DIV":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            ssa_op_dict[var_name] = i+1
            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "LT":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            ssa_op_dict[var_name] = i+1
            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "SMOD":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            ssa_op_dict[var_name] = i+1
            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "SIGNEXTEND":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            var_name = "%"+str(var_count)

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "MOD":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            ssa_op_dict[var_name] = i+1
            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "SGT":
            #operands from stack swapped to form sgt check
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            ssa_op_dict[var_name] = i+1
            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "GT":
            #operands from stack swapped to form gt check
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)

            if "%" not in str(stack[0]) and "%" not in str(stack[1]):
                print("Constant synthesis candidate at: ",i," (",target[i],")")

            ssa_op_dict[var_name] = i+1
            stack = _stack_pop(target[i], stack)
            stack.insert(0, var_name)
            var_increment = True
            j_prev = False

        elif target[i] == "CALLDATACOPY":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            j_prev = False

        elif target[i] == "EXTCODECOPY":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            j_prev = False

        elif target[i] == "CALLDATALOAD":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False
            

        
#----------------------Stack related ops that require symbolic var----------------------#
        
        elif target[i] == "ADDRESS":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "BALANCE":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "ORIGIN":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "EXTCODESIZE":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "BLOCKHASH":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "COINBASE":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "TIMESTAMP":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "NUMBER":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "DIFFICULTY":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "GASLIMIT":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "PC":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "GAS":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "MLOAD":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "CREATE":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "CALL":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "CALLCODE":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "DELEGATECALL":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "SLOAD":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "MSIZE":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "CALLDATASIZE":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "KECCAK256":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "SHA3":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "CALLVALUE":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "CALLER":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "RETURNDATACOPY":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            j_prev = False

        elif target[i] == "RETURNDATASIZE":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False

        elif target[i] == "ISZERO":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            var_name = "%"+str(var_count)
            ssa_op_dict[var_name] = i+1
            stack.insert(0, var_name)
            var_dict[var_name] = target[i]
            var_increment = True
            j_prev = False


#---------------------------------Store ops----------------------------------------#
        elif "STORE" in target[i]:
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(_clean_opcode(target[i]), stack)
            j_prev = False

        elif "LOG" in target[i]:
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            stack = _stack_pop(target[i], stack)
            j_prev = False


#-------------------------------------JUMP ops---------------------------------------#

        elif target[i] == "JUMPDEST":
            if j_prev == False:
                g.add_edge(block_map[i-1],block_map[i])
                call_history.append(block_map[i-1])
            j_prev = False

        elif target[i] == "JUMP":
            global_dependants.extend(get_dependencies_long(i, target[i], target))
            if "%" in str(stack[0]):
                print("DYNAMIC JUMP at line ",i)
                global_state.append([i,block_map[i],list(stack),[dest],call_history])
                call_history = []
                break
            else:
                try:
                    dest = hfs_op_map[(stack[0])]
                    g.add_edge(block_map[i],block_map[dest])
                    call_history.append(block_map[i])
                    j_prev = True
                except:
                    print("Bad JUMPDEST passed to  JUMP at ",i)
                    global_state.append([i,block_map[i],list(stack),[],call_history])
                    call_history = []
                    break 
                jump_dest_lst.insert(0, dest)
                if len(jump_dest_lst) > 1:
                    if dest == jump_dest_lst[1]:
                        if dest != 0:
                            global_state.append([i,block_map[i],list(stack),[dest],call_history])
                        else:
                            global_state.append([i,block_map[i],list(stack),[],call_history])
                        call_history = []
                        break
                stack = _stack_pop(target[i], stack)
                i = dest-1

            
        elif target[i] == "JUMPI":
            if "%" in str(stack[1]):
                if "%" in str(stack[0]):
                    print("DYNAMIC JUMP", i)
                    global_state.append([i,block_map[i],list(stack),[dest],call_history])
                    g.add_edge(block_map[i],block_map[i+1])
                    call_history.append(block_map[i])
                    print("EX called from DYNAMIC")
                    stack = _stack_pop(target[i], stack)
                    j_prev = False
                    sym_ex(source_file, i+1, list(stack), var_count, list(call_history), j_prev)
                    call_history = []
                    break
                else:
                    try:
                        dest = hfs_op_map[(stack[0])]
                    except:
                        print("Bad JUMPDEST passed to JUMPI at ",i)
                        global_state.append([i,block_map[i],list(stack),[dest],call_history])
                        call_history.append(block_map[i])
                        g.add_edge(block_map[i],block_map[i+1])
                        stack = _stack_pop(target[i], stack)
                        j_prev = False
                        sym_ex(source_file, i+1, list(stack), var_count, list(call_history), j_prev)
                        call_history = []
                        break
                    if len(jumpi_dest_lst) > 1:
                        if (dest,i) in jumpi_dest_lst:
                            global_state.append([i,block_map[i],list(stack),[dest],call_history])
                            print("RE-ENTRY DETECTED (JUMPI/DEST): ",block_map[i],", ",block_map[dest])
                            call_history = []
                            break
                    jumpi_dest_lst.insert(0, (dest,i))
                    global_state.append([i,block_map[i],list(stack),[dest],call_history])
                    g.add_edge(block_map[i],block_map[dest])
                    g.add_edge(block_map[i],block_map[i+1])
                    call_history.append(block_map[i])
                    stack = _stack_pop(target[i], stack)
                    j_prev = True
                    sym_ex(source_file, dest, list(stack), var_count, list(call_history), j_prev)
                    sym_ex(source_file, i+1, list(stack), var_count, list(call_history), j_prev)
            elif str(stack[1])=="True" or str(stack[1])=="1":
                if "%" in str(stack[0]):
                    print("DYNAMIC JUMP", i)
                    global_state.append([i,block_map[i],list(stack),[dest],call_history])
                    g.add_edge(block_map[i],block_map[i+1])
                    print("EX called from DYNAMIC")
                    stack = _stack_pop(target[i], stack)
                    call_history.append(block_map[i])
                    call_history = []
                    break
                else:
                    try:
                        dest = hfs_op_map[(stack[0])]
                    except:
                        print("Bad JUMPDEST passed to JUMPI at ",i)
                        global_state.append([i,block_map[i],list(stack),[dest],call_history])
                        g.add_edge(block_map[i],block_map[i+1])
                        stack = _stack_pop(target[i], stack)
                        call_history.append(block_map[i])
                        call_history = []
                        break
                    if len(jumpi_dest_lst) > 1:
                        if (dest,i) in jumpi_dest_lst:
                            global_state.append([i,block_map[i],list(stack),[dest],call_history])
                            print("RE-ENTRY DETECTED (JUMPI/DEST): ",block_map[i],", ",block_map[dest])
                            call_history = []
                            break
                    jumpi_dest_lst.insert(0, (dest,i))
                    global_state.append([i,block_map[i],list(stack),[dest],call_history])
                    g.add_edge(block_map[i],block_map[dest])
                    call_history.append(block_map[i])
                    stack = _stack_pop(target[i], stack)
                    j_prev = True
                    sym_ex(source_file, dest, list(stack), var_count, list(call_history), j_prev)
                    call_history.append(block_map[i])
            elif str(stack[1])=="False" or str(stack[1]=="0"):
                if len(jumpi_dest_lst) > 1:
                    if (dest,i) in jumpi_dest_lst:
                        g.add_edge(block_map[i],block_map[dest])
                        global_state.append([i,block_map[i],list(stack),[dest],call_history])
                        print("RE-ENTRY DETECTED (JUMPI/DEST): ",block_map[i],", ",block_map[dest])
                        call_history = []
                        break
                jumpi_dest_lst.insert(0, (dest,i))
                global_state.append([i,block_map[i],list(stack),[dest],call_history])
                g.add_edge(block_map[i],block_map[i+1])
                call_history.append(block_map[i])
                stack = _stack_pop(target[i], stack)
                j_prev = True
                sym_ex(source_file, i+1, list(stack), var_count, list(call_history), j_prev)
            else:
                print("JUMPI ERROR!: ",stack[1])
            call_history = []
            break


        elif target[i] == "RETURN":
            global_state.append([i,block_map[i],list(stack),[],call_history])
            call_history = []
            break

        elif target[i] == "STOP":
            global_state.append([i,block_map[i],list(stack),[],call_history])
            call_history = []
            break

        elif target[i] == "REVERT":
            global_state.append([i,block_map[i],list(stack),[],call_history])
            call_history = []
            break

        elif target[i] == "SUICIDE":
            global_state.append([i,block_map[i],list(stack),[],call_history])
            call_history = []
            break

        elif target[i] == "SELFDESTRUCT":
            global_state.append([i,block_map[i],list(stack),[],call_history])
            call_history = []
            break

        elif target[i] == "INVALID":
            global_state.append([i,block_map[i],list(stack),[],call_history])
            call_history = []
            break

        else:
            print(i,": ",target[i])


        if var_increment==True:
            var_count+=1

        if (target[i] == "JUMP") or (target[i] == "JUMPI"):
            global_state.append([i,block_map[i],list(stack),[dest],call_history])
        else:
            global_state.append([i,block_map[i],list(stack),[],call_history])

        i+=1


#Uncomment a line below to run with one of the test files

#target_file = "translation_greeter_mortal_remix_op_rt.op"
#target_file = "translation_multisig_remix_rt.op"
target_file = "translation_SimpleCoinToken.op"
#target_file = "translation_remix_GolemMultisig_0x7da82C7AB4771ff031b66538D2fB9b0B047f6CF9.op"
#target_file = "translation_RaidenMultiSigWallet_0x00C7122633A4EF0BC72f7D02456EE2B11E97561e.op"

#------------------------------------------------------------#

sym_ex(target_file)


with open(target_file, "r") as f:
        lines = f.read().splitlines()
        y = len(lines)

with open("info_"+target_file[:-2]+"pickle", "wb") as f:
    pickle.dump(global_state, f, protocol=2)

nx.draw(g,pos=nx.spring_layout(g),with_labels=True)
#nx.write_yaml(g,target_file+"_graph.yaml")

with open("graph_"+target_file[:-2]+"json", "w") as f:
    f.write(json.dumps(nx.readwrite.node_link_data(g)))

code_coverage = (nx.number_of_nodes(g)/(block_total+1))*100
gd = nx.descendants(g,0)
print(code_coverage)
print("No of blocks ",block_total+1)
print("nodes: ",nx.number_of_nodes(g))
print("Number of loops: ",len(list(nx.simple_cycles(g))))


plt.show()