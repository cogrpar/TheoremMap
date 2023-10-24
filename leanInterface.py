# this file contains tools for interfacing python and lean4
import subprocess
from typing import Callable


# below is a function that runs a command passed as a string and returns the output as a string
def runCommand (command : str) -> str:
    return subprocess.run(command, stdout=subprocess.PIPE, shell=True).stdout.decode('utf-8')

# below is a function to run a lean 4 script stored in a string and get the output as a string
def runLeanString (leanScript : str) -> str:
    with open('./tmp.lean', 'w') as l:
        l.write(leanScript)
    command = 'lake env lean ./tmp.lean'
    return runCommand(command)

# below is a class used to represent general lean 4 objects using dependent type theory
class LeanObject:
    def __init__(self, name : str, lean_type : str = None, value : str | int | float | bool | list = 'sorry', requiredImports : list[str] = []):
        self.name = name
        self.requiredImports = requiredImports

        # if a type is not provided, try to infer it using lean
        if lean_type == None:
            check = runLeanString(f'''
                import LeanBackend
                {' '.join(f'import {package}' for package in self.requiredImports)}
                #check @{name}
            ''')
            # if the variable can not be found by lean then raise an error
            if f'error: unknown identifier \'{name}\'' in check or 'unknown namespace' in check or 'unknown constant' in check:
                raise NameError(f'unknown lean identifier {name}')
            # if the required package could not be found by lean then raise an error
            elif 'unknown package' in check:
                raise ImportError(f'{check}: lean can\'t find the package you provided')
            else:
                lean_type = check.replace(f'{name} : ', '').strip('\n')
        self.type = lean_type

        # if a value is not provided, try to infer it using lean
        if value == 'sorry':
            try:
                if self.type == 'Nat' or self.type == 'Int':
                    self.value = int(runLeanString(f'''
                        import LeanBackend
                        {' '.join(f'import {package}' for package in self.requiredImports)}
                        #eval {name}
                    '''))
                elif self.type == 'Float':
                    self.value = float(runLeanString(f'''
                        import LeanBackend
                        {' '.join(f'import {package}' for package in self.requiredImports)}
                        #eval {name}
                    '''))
                elif self.type == 'Bool':
                    self.value = True if runLeanString(f'''
                        import LeanBackend
                        {' '.join(f'import {package}' for package in self.requiredImports)}
                        #eval {name}
                    ''') == 'true' else False
                elif self.type.startswith('Array ') or self.type.startswith('List ') and not '→' in self.type:
                    self.value = runLeanString(f'''
                        import LeanBackend
                        {' '.join(f'import {package}' for package in self.requiredImports)}
                        #eval {name}
                    ''').replace(' ', '').replace('[', '').replace(']', '').replace('#[', '').split(',')
                else:
                    value = runLeanString(f'''
                        import LeanBackend
                        {' '.join(f'import {package}' for package in self.requiredImports)}
                        #print {name}
                    ''')
                    value = ':='.join(value.split(':=')[1:])

                    self.value = value
                    if 'failed to be synthesized' in self.value:
                        raise TypeError(f'The value of {self.name} could not be synthesized')
            except:
                value = runLeanString(f'''
                    import LeanBackend
                    {' '.join(f'import {package}' for package in self.requiredImports)}
                    #print {name}
                ''')
                value = ':='.join(value.split(':=')[1:])
                
                self.value = value
                if 'failed to be synthesized' in self.value:
                    raise TypeError(f'The value of {self.name} could not be synthesized')


        else:
            self.value = value
    
    def functionality(self, *args) -> tuple[str, str]:
        outputType = runLeanString(f'''
            import LeanBackend
            {' '.join(f'import {package}' for package in self.requiredImports)}
            #check {self.name} {" ".join(map(lambda arg : arg.value if type(arg.value) in [int, float] 
                                                                    else 'true' if arg.value == True
                                                                    else 'false' if arg.value == False
                                                                    else '"' + str(arg.value) + '"' if type(arg.value) in [str, list]
                                                                    else '', args))}
        ''')
        outputValue = runLeanString(f'''
            import LeanBackend
            {' '.join(f'import {package}' for package in self.requiredImports)}
            #eval {self.name} {" ".join(map(lambda arg : arg.value if type(arg.value) in [int, float] 
                                                                    else 'true' if arg.value == True
                                                                    else 'false' if arg.value == False
                                                                    else '"' + str(arg.value) + '"' if type(arg.value) in [str, list]
                                                                    else '', args))}         
        ''')

        # possible errors to check for:
        # 1. unknown identifier '[variable name]' (if the variable doesn't exist in lean)
        # 2. argument [arg.name] has type [arg.type] but is expected to have type [correct type] (if the type of the argument is wrong)
        # 3. unknown package [requiredImport] (if lean can't find a required import)
        if 'unknown identifier' in outputType or 'unknown namespace' in outputType or 'unknown constant' in outputType:
            raise NameError('unknown lean identifier')

        elif 'but is expected to have type' in outputType:
            raise TypeError(f'incorrect type for lean identifier {self.name}')
        elif 'unknown package' in outputType:
            raise ImportError(f'{outputType}: lean can\'t find the package you provided')
        else:
            outputType = outputType.replace('\n', ' ').split(' : ')[-1].strip()
            outputValue = outputValue.replace('\n', ' ').strip()

            # cast the output to the correct type
            try:
                if outputType == 'Nat' or outputType == 'Int':
                    outputValue = int(outputValue)
                elif outputType == 'Float':
                    outputValue = float(outputValue)
                elif outputType == 'Bool':
                    outputValue = True if outputValue == 'true' else False
                elif 'Array ' in outputType or 'List ' in outputType:
                    outputValue = outputValue.replace(' ', '').replace('[', '').replace(']', '').replace('#[', '').split(',')
                elif outputType == 'String':
                    outputValue = outputValue.strip('"')
            except:
                outputValue = outputValue.strip('"')

            # return the output type and value
            return outputType, outputValue
        
    def overrideFunctionality (self, func: Callable) -> tuple[str, str]:
        # this function can be used to override __call__ functionality by passing an alternative function
        # this allows for a function to be implemented in python rather than lean
        self.functionality = func

    def __call__ (self, *args) -> tuple[str, str]:
        return self.functionality(*args)

# below is a class used to store lean 4 theorems, which are just objects where the type is a proposition, and the existence of the object represents that it has been proven
class LeanTheorem (LeanObject):
    def __init__(self, name : str, lean_prop : str = None, proof : str | int | float | bool | list = 'sorry', requiredImports : list[str] = []):
        super().__init__(name, lean_prop, proof, requiredImports)
        self.prop = self.type
        self.proof = self.value

    def __str__(self):
        return self.name + ' : ' + self.prop + ' := ' + str(self.proof)
    
# below is a class used to store lean 4 definitions, which here are just objects that are not theorems
class LeanDef (LeanObject):
    def __init__(self, name : str, lean_type : str = None, value : str | int | float | bool | list = 'sorry', requiredImports : list[str] = []):
        super().__init__(name, lean_type, value, requiredImports)

    def __str__(self):
        return self.name + ' : ' + self.type + ' := ' + str(self.value)
    
# this function cleans up by removing 'tmp.lean'
def cleanup():
    runCommand('rm ./tmp.lean')