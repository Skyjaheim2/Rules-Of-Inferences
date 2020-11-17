import os
from flask import Flask, render_template, request, redirect, session
from flask_session import Session
from random import randint
import smtplib
from email.message import EmailMessage


from tempfile import mkdtemp
import hashlib
import mysql.connector
from datetime import date
current_date = date.today()
now = current_date.strftime("%B %d, %Y")


app = Flask(__name__)
# Configure session to use filesystem (instead of signed cookies)
app.config["SESSION_FILE_DIR"] = mkdtemp()
app.config["SESSION_PERMANENT"] = False
app.config["SESSION_TYPE"] = "filesystem"
Session(app)

# ENABLE SESSION
Session(app)

CONJUNCTION = '^'
DISJUNCTION = 'v'
IMPLICATION = '→'
NEGATION    = '¬'

ALL_SYMBOLS = [CONJUNCTION, DISJUNCTION, IMPLICATION, NEGATION]


Testing = False

@app.route('/')
def index():
    return render_template('index.html', check_index=False)

@app.route('/solve', methods=['POST'])
def solve():
    premises = request.form.get('premises').strip()
    premises = premises.split(',')

    final_conclusion = request.form.get('final_conclusion').strip()

    final_conclusion = final_conclusion.replace('/neg', NEGATION).replace('/wedge', CONJUNCTION).replace('/vee', DISJUNCTION).replace('/arrow', IMPLICATION)

    Premises = []

    for item in premises:
        prem = item.replace('/neg', NEGATION).replace('/wedge', CONJUNCTION).replace('/vee', DISJUNCTION).replace('/arrow', IMPLICATION).strip()
        Premises.append(prem)

    temp = [item for item in Premises]

    tempRules = rules_of_inferences(Premises, final_conclusion, temp)

    if not tempRules:
        return render_template('index.html', premises=temp, final_conclusion=final_conclusion, error=True)


    newConclusions = tempRules[0]
    finalResult = tempRules[1]
    conclusions = tempRules[2]

    return render_template('index.html', premises=temp, final_conclusion=final_conclusion, newConclusions=newConclusions, finalResult=finalResult, conclusions=conclusions, indexOf=indexOf, check_index=True)




MAX_RUN_TIME = 50
run_time = 0
def rules_of_inferences(premises: list, finalConclusion, premises_at_first_run_time):
    global run_time
    conclusions = {}
    single_premises = []
    string_of_premises = ""
    for prem in premises:
        string_of_premises += prem

    for i, premise in enumerate(premises):

        # string_of_premises += premise
        # CHECK FOR SIMPLIFICATION
        if CONJUNCTION in premise:
            if len(Simplification(premise)) <= len(premise.split(CONJUNCTION)):
                for item in Simplification(premise):
                    if item not in premises_at_first_run_time:
                        conclusions.update({item: f'Simplification on ({premise})'})
            else:
                for item in Simplification(premise):
                    if item not in premises_at_first_run_time and item in string_of_premises or item in finalConclusion:
                        conclusions.update({item: f'Simplification on ({premise})'})

        # CHECK FOR CONJUNCTION
        if is_single_proposition(premise):
            single_premises.append(premise)
        if len(single_premises) >= 2:
            for item in Conjunction(single_premises):
                if item in string_of_premises and item not in conclusions and item not in premises_at_first_run_time and is_single_proposition(
                        item):
                    conclusions.update({
                                           item: f"Conjunction on ({item.split(CONJUNCTION)[0].replace(' ', '')}) and ({item.split(CONJUNCTION)[1].replace(' ', '')})"})

        if IMPLICATION in premise:
            implication_variables = premise.split(IMPLICATION) if len(premise.split(IMPLICATION)) == 2 else splitCompoundImplication(premise)
            # CHECK FOR MODUS PONENS
            tempMP = ModusPonens(implication_variables, premises)
            for item in tempMP:
                conclusions.update({item: f'Modus Pones on ({premise}) and ({tempMP[item]})'})
            # CHECK FOR HYPOTHETICAL SYLLOGISM
            tempHS = HypotheticalSyllogism(implication_variables, premise, premises)
            for item in tempHS:
                conclusions.update(
                    {f'{item}': f"Hypothetical Syllogism on ({tempHS[item][0]}) and ({tempHS[item][1]})"})
            # DO IMPLICATION LAW
            tempIL = ImplicationLaw(premise)
            for item in tempIL:
                if item in string_of_premises or item == finalConclusion:
                    conclusions.update({item: f"Implication-Law on ({tempIL[item]})"})
            # DO CONTRAPOSITIVE
            tempCP = Contrapositive(implication_variables)
            if (tempCP in string_of_premises and tempCP not in premises_at_first_run_time) or tempCP in finalConclusion:
                conclusions.update({tempCP: f"Contrapositive on ({tempCP})"})

        if NEGATION in premise:
            negated_variable = premise
            # CHECK FOR MODUS TOLLENS
            if is_single_proposition(premise):
                tempMT = ModusTollens(negated_variable, premises)
                for item in tempMT:
                    conclusions.update({item: f"Modus Tollens on ({premise}) and ({tempMT[item]})"})
            # CHECK FOR IMPLICATION
            if DISJUNCTION in premise:
                tempIL = ImplicationLaw(premise)
                for item in tempIL:
                    conclusions.update({item: f"Implication-Law on ({tempIL[item]})"})
            # CHECK FOR DOUBLE NEGATION
            neg_count = 0
            for char in premise:
                if char == NEGATION:
                    neg_count += 1
            if neg_count == 2:
                tempDN = DoubleNegation(premise)
                for item in tempDN:
                    conclusions.update({item: f"Double-Negation on ({tempDN[item]})"})

        if DISJUNCTION in premise:
            # CHECK FOR DISJUNCTIVE SYLLOGISM
            if is_single_proposition(premise):
                tempDS = DisjunctiveSyllogism(premise, premises)
                for item in tempDS:
                    conclusions.update({item: f"Disjunctive Syllogism on ({premise}) and ({tempDS[item]})"})
            # CHECK FOR RESOLUTION
            tempR = Resolution(premise, premises)
            for item in tempR:
                conclusions.update({item: f"Resolution on ({tempR[item][0]}) and ({tempR[item][1]})"})

    for conclusion in conclusions:
        premises.append(conclusion)

    newConclusions = premises
    newConclusions = removeDuplicates(newConclusions)


    if not Testing:
        for conclusion in newConclusions:
            if conclusion == finalConclusion or conclusion == finalConclusion.replace('(', '').replace(')', '') or finalConclusion == switchConclusions(conclusion):
                finalResult = {}
                for i, item in enumerate(newConclusions, 1):
                    finalResult.update({f'({item})': i})

                return [newConclusions, finalResult, conclusions]


        if run_time < MAX_RUN_TIME:
            run_time += 1
            return rules_of_inferences(newConclusions, finalConclusion, premises_at_first_run_time)

        return False







def Simplification(premise):
    if validSimplification(premise):
        if computeOccurences(premise, CONJUNCTION) == 1:
            first_conjunction = premise.split(CONJUNCTION)[0].strip()
            second_conjunction =  premise.split(CONJUNCTION)[1].strip()
            return [remove_paren(first_conjunction) if is_single_proposition(first_conjunction) else first_conjunction, remove_paren(second_conjunction) if is_single_proposition(second_conjunction) else second_conjunction]
        else:
            all_combinations = getAllConjunctions(premise)
            return all_combinations
    else:
        return []
def validSimplification(premise):
    if computeOccurences(premise, CONJUNCTION) == 1:
        if is_single_proposition(premise):
            return True
        else:
            prop = premise.split(CONJUNCTION)

            first_prop = prop[0].strip()
            second_prop = prop[1].strip()

            return paren_is_balanced(first_prop) and paren_is_balanced(second_prop)

    else:
        # GET ALL SYMBOLS EXCEPT CONJUNCTION
        tempSymbols = []
        for symbol in ALL_SYMBOLS:
            if symbol != CONJUNCTION:
                tempSymbols += symbol
        # IF THERE ARE ANY OF SYMBOLS OTHER THAN CONJUNCTION, THEN ITS NO LONGER VALID BECAUSE IT LOSES IT ASSOCIATIVITY
        for char in premise:
            if char in tempSymbols:
                return False
        return True
def getAllConjunctions(premise):
    temp_premise = premise
    premise = premise.replace('(', '').replace(')', '').split(CONJUNCTION)


    for i, char in enumerate(temp_premise):
        if char == CONJUNCTION:
            left_prop  = temp_premise[:i].strip()
            right_prop = temp_premise[i+1:].strip()
            if paren_is_balanced(left_prop) and paren_is_balanced(right_prop):
                stride_index = i



    first_conjunction  = temp_premise[:stride_index-1].replace('(', '').replace(')', '') if is_single_proposition(temp_premise[:stride_index-1]) else temp_premise[:stride_index-1]
    second_conjunction = temp_premise[stride_index+2:].replace('(', '').replace(')', '') if is_single_proposition(temp_premise[stride_index+2:]) else temp_premise[stride_index+2:]

    all_combinations = [first_conjunction, second_conjunction]


    for i in range(len(premise)):
        for j in range(len(premise)):
            if premise[i].strip() != premise[j].strip():
                all_combinations.append(f'{premise[i].strip()} {CONJUNCTION} {premise[j].strip()}')

    return removeDuplicates(all_combinations)

def ModusPonens(impl_variables, premises):
    hypothesis = impl_variables[0].strip().replace('(', '').replace(')', '')
    # ONLY REMOVE THE () IF ITS A SINGLE PROPOSITION
    consequent = impl_variables[1].strip().replace(')', '').replace('(', '') if is_single_proposition(impl_variables[1].strip()) else impl_variables[1].strip()

    new_conclusions_to_return = {}

    for premise in premises:
        if premise == hypothesis or premise.replace('(', '').replace(')', '') == hypothesis:
            new_conclusions_to_return.update({consequent: premise})

    return new_conclusions_to_return

def ModusTollens(neg_variable, premises):
    reg_variable = neg_variable[1:]

    new_conclusions_to_return = {}

    for premise in premises:
        if IMPLICATION in premise:
            hypothesis = premise.split(IMPLICATION)[0].strip().replace('(', '')
            consequent = premise.split(IMPLICATION)[1].strip()
            if reg_variable == consequent:
                negated_hypothesis = f'{NEGATION}{hypothesis}'
                new_conclusions_to_return.update({negated_hypothesis: premise})

    return new_conclusions_to_return

def DisjunctiveSyllogism(premise_given, premises):
    first_disjunction_var  = premise_given.split(DISJUNCTION)[0].strip().replace('(', '').replace(')', '') if is_single_proposition(premise_given.split(DISJUNCTION)[0].strip()) else premise_given.split(DISJUNCTION)[0].strip()
    # second_disjunction_var = premise_given.split(DISJUNCTION)[1].strip()
    second_disjunction_var = premise_given[indexOf(premise_given, DISJUNCTION)+2:].replace('(', '').replace(')', '') if is_single_proposition(premise_given[indexOf(premise_given, DISJUNCTION)+2:]) else premise_given[indexOf(premise_given, DISJUNCTION)+2:]

    new_conclusions_to_return = {}

    for premise in premises:
        negated_variables = []
        if NEGATION in premise and is_single_proposition(premise):
            negated_variables.append(premise)
        # CHECK FOR ANY NEGATED VARIABLES
        for neg_var in negated_variables:
            reg_var = neg_var[1:]
            if first_disjunction_var == reg_var:
                new_conclusions_to_return.update({second_disjunction_var: neg_var})
            elif second_disjunction_var == reg_var:
                new_conclusions_to_return.update({first_disjunction_var: neg_var})

    return new_conclusions_to_return

def Conjunction(single_premises: list):
    new_conclusions_to_return = []
    for i in range(len(single_premises)):
        for j in range(len(single_premises)):
            if single_premises[i] != single_premises[j]:
                conjunction = f'{single_premises[i]} {CONJUNCTION} {single_premises[j]}'
                new_conclusions_to_return.append(conjunction)

    new_conclusions_to_return = removeDuplicates(new_conclusions_to_return)
    return new_conclusions_to_return


def HypotheticalSyllogism(impl_variables, implication, premises):
    hypothesis = impl_variables[0].strip().replace('(', '')
    consequent = impl_variables[1].strip().replace(')', '')

    new_conclusions_to_return = {}
    for premise in premises:
        if IMPLICATION in premise and premise != implication:
            next_hypothesis = premise.split(IMPLICATION)[0].strip().replace('(', '')
            next_consequent = premise.split(IMPLICATION)[1].strip().replace(')', '')

            if next_hypothesis == consequent:
                new_implication = f"{hypothesis} {IMPLICATION} {next_consequent}"
                new_conclusions_to_return.update({new_implication: [implication, premise]})


    return new_conclusions_to_return


def Resolution(premise_given, premises):
    first_disjunction  = premise_given.split(DISJUNCTION)[0].strip()
    second_disjunction = premise_given.split(DISJUNCTION)[1].strip()

    new_conclusions_to_return = {}


    for premise in premises:
        if DISJUNCTION in premise and premise != premise_given:
            next_first_disjunction  = premise.split(DISJUNCTION)[0].strip()
            next_second_disjunction = premise.split(DISJUNCTION)[1].strip()
            # CHECK FIRST DISJUNCTION AGAINST ALL PREMISES
            if NEGATION in next_first_disjunction:
                reg_var = next_first_disjunction[1]
                if reg_var == first_disjunction:
                    new_conclusions_to_return.update({f"{second_disjunction} {DISJUNCTION} {next_second_disjunction}": [premise_given, premise]})
            # CHECK SECOND DISJUNCTION AGAINST ALL PREMISES
            if NEGATION in next_second_disjunction:
                reg_var = next_second_disjunction[1]
                if reg_var == second_disjunction:
                    new_conclusions_to_return.update({f"{first_disjunction} {DISJUNCTION} {next_first_disjunction}": [premise_given, premise]})

    return new_conclusions_to_return

def Contrapositive(impl_variables):
    hypothesis = impl_variables[0].strip().replace('(', '')
    consequent = impl_variables[1].strip().replace(')', '')

    contrapositive = f'{NEGATION}{consequent} {IMPLICATION} {NEGATION}{hypothesis}'

    return contrapositive

def IdempotentLaw(premises):
    if CONJUNCTION in premises:
        found = False
        new_conclusions_to_return = []
        first_conjunction = premises.split(CONJUNCTION)[0].strip().replace('(', '')
        second_conjunction = premises.split(CONJUNCTION)[1].strip().replace(')', '')

        if first_conjunction == second_conjunction:
            found = True
            new_conclusions_to_return.append(first_conjunction)
        return [new_conclusions_to_return, found]

def DoubleNegation(premise):
    conclusions_to_return = {}
    double_negation = f"{NEGATION}{NEGATION}"
    prop_variables = premise.split()
    for i, var in enumerate(prop_variables):
        if double_negation in var:
            new_var = var[2:]
            prop_variables[i] = new_var
            new_proposition = f""
            for item in prop_variables:
                new_proposition += item
                new_proposition += " "
            new_proposition = new_proposition.rstrip()
            conclusions_to_return.update({new_proposition: premise})

    return conclusions_to_return

def ImplicationLaw(premise):
    conclusion_to_return = {}

    if IMPLICATION in premise:
        hypothesis = premise.split(IMPLICATION)[0].strip().replace('(', '').replace(')','')
        consequent = premise.split(IMPLICATION)[1].strip().replace('(', '').replace(')','') if is_single_proposition(premise) else premise.split(IMPLICATION)[1].strip()

        new_proposition = f"{NEGATION}{hypothesis} {DISJUNCTION} {consequent}"

        conclusion_to_return.update({new_proposition: premise})

        return conclusion_to_return

    if DISJUNCTION in premise:
        reg_var = premise[indexOf(premise, NEGATION)+1: indexOf(premise, DISJUNCTION)-1]
        second_disjunction_var = premise[indexOf(premise, DISJUNCTION) + 2:].replace('(', '').replace(')','') if is_single_proposition(premise[indexOf(premise, DISJUNCTION) + 2:]) else premise[indexOf(premise, DISJUNCTION) + 2:]

        new_proposition = f"{reg_var} {IMPLICATION} {second_disjunction_var}"
        conclusion_to_return.update({new_proposition: premise})

        return conclusion_to_return


    return conclusion_to_return

def switchConclusions(conclusion):
    if is_single_proposition(conclusion):
        if CONJUNCTION in conclusion:
            first_prop  = conclusion.split(CONJUNCTION)[0].strip()
            second_prop = conclusion.split(CONJUNCTION)[1].strip()

            new_conclusion = f'{second_prop} {CONJUNCTION} {first_prop}'
            return new_conclusion
        elif DISJUNCTION in conclusion:
            first_prop = conclusion.split(DISJUNCTION)[0].strip()
            second_prop = conclusion.split(DISJUNCTION)[1].strip()

            new_conclusion = f'{second_prop} {DISJUNCTION} {first_prop}'
            return new_conclusion
        else:
            return None
    return None
def splitCompoundImplication(premise):
    implication_occurrences = 0
    for i, char in enumerate(premise):
        if char == IMPLICATION:
            implication_occurrences += 1
            left_prop = premise[:indexOf(premise, IMPLICATION, implication_occurrences)-1]
            right_prop = premise[indexOf(premise, IMPLICATION, implication_occurrences)+2:]
            if is_single_proposition(left_prop) and is_single_proposition(right_prop):
                return [left_prop, right_prop]

    return []



def removeDuplicates(array):
    found_items = []
    for item in array:
        if item not in found_items:
            found_items.append(item)

    return found_items
def is_single_proposition(premise):
    count = 0
    premise = premise.split()
    for char in premise:
        if char in ALL_SYMBOLS:
            count += 1

    return count <= 1
def indexOf(string, index_of, specific_index=None):
    if specific_index != None:
        all_occurrences = []

        for i in range(len(string)):
            if string[i] == index_of:
                all_occurrences.append(i)

        return all_occurrences[specific_index - 1] if len(all_occurrences) != 0 else None
    for i in range(len(string)):
        if string[i] == index_of:
            return i
def paren_is_balanced(premise):
    open_paren   = ['(', '[', '{']
    closed_paren = [')', ']', '}']


    open_paren_in_str = [item for item in premise if item in open_paren]
    closed_paren_in_string = [item for item in premise if item in closed_paren]


    return len(open_paren_in_str) == len(closed_paren_in_string)

def remove_paren(string):
    return string.replace('(', '').replace(')', '')
def computeOccurences(string: str, occurence):
    index = 0
    for char in string:
        if char == occurence:
            index += 1

    return index


@app.route("/test")
def test():
    dict = {
        'dog': 'A dog has four legs',
        'cat': 'A cat has four legs',
    }

    array = ['Jaheim', 'John', 'Jimmy']
    num_array = [1,2,3,4,5,6,7,8,9,10,11,12]

    return render_template('test.html', test_item=array)




if __name__ == '__main__':
    app.run(debug=True)