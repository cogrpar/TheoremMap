# this file generates ObjectList.json
from leanInterface import *
import os
import re

# below is a LeanDef that stores a list of all objects that will be considered when constructing the theorem map
# the list is generated using the generateObjectList function, which takes a list of file paths containing lean files to consider
# the list itself stores the following information for each object:
#   1. the object name as a string
#   2. the object type as a string
#   3. the object lean import path as a string

# the following function is used by generateObjectList to extract all lean objects from a given .lean file
def extractLeanObjects (filePath : str) -> list[str]:
    objects = [] # will store a list of object defs
    with open(filePath) as file:
        text = file.read()
        # remove comments
        singleLinCommentPattern = re.escape('--') + r'(.*?)' + re.escape('\n')
        multipleLineCommentPattern = re.escape('OPEN_COMMENT') + r'(.*?)' + re.escape('CLOSE_COMMENT')
        stringPattern = re.escape('"') + r'(.*?)' + re.escape('"')
        text = text.replace('/-', 'OPEN_COMMENT').replace('-/', 'CLOSE_COMMENT')
        text = re.sub(singleLinCommentPattern, '', text)
        text = text.replace('\n', ' ')
        text = re.sub(multipleLineCommentPattern, '', text)
        text = re.sub(stringPattern, '', text)
        words = ['PAD'] * 3 + text.split(' ') + ['PAD'] * 3

    # deal with possible cases for file_path
    # 1. Lean toolchain path (ie. [home directory]/.elan/toolchains/leanprover--lean4---[version]/src/lean)
    #   - only lean files in sub-folders can be accessed
    #   - the import is formatted as [subfolder1].[subfolder2]...[subfolderN].[file]
    if '.elan/toolchains/' in filePath:
        # ignore files not in sub-folders
        if filePath.split('/')[-3] == 'src' and filePath.split('/')[-2] == 'lean':
            return ['']
        importPath = filePath.split('/src/lean/')[-1].replace('/', '.').rstrip('lean').rstrip('.')

    # 2. lake-packages path (ie. ./lake-packages)
    #   - the import must be at least 1 folder deep, and the first subfolder name is not included in the import path
    #   - all further imports must be in a folder with the same name as the main lean file
    #   - if the main lean file is called Package.lean the import is formatted as [Package]...[subfolderN].[file]
    elif 'lake-packages' in filePath:
        # get the main lean file name(s)
        mainFiles = []
        packageBasePath = '/'.join(filePath.split('/')[:filePath.split('/').index('lake-packages')+2])
        for file in os.listdir(packageBasePath):
            if file.endswith('.lean') and file != 'lakefile.lean':
                mainFiles.append(os.path.join(packageBasePath, file.rstrip('.lean')))
        # ignore lakefiles and other files not in the main package file structure
        if filePath.endswith('/lakefile.lean') or not any(mainFile in filePath for mainFile in mainFiles):
            return ['']
        else:
            importPath = '.'.join(filePath.split('lake-packages/')[1].split('/')[1:]).rstrip('lean').rstrip('.')

    # 3. LeanBackend path (ie. ./LeanBackend)
    #   - the imports path is the same as the relative path
    elif 'LeanBackend' in filePath:
        importPath = filePath.split('/LeanBackend/')[-1].replace('/', '.').rstrip('lean').rstrip('.')
    
    else:
        raise ValueError(
            f'the provided file path, \'{filePath}\', could not be found in the toolchain code base, the lake-packages, or as part of the LeanBackend package'
            )

    objects.append(importPath)
    
    # iterate through the file, keeping track of namespaces 
    # once an object is encountered (def, theorem, or instance), get the type by wrapping it in a LeanDef or LeanTheorem object
    namespaces = []
    for wordNum, word in enumerate(words):
        if word == 'namespace':
            namespaces += words[wordNum+1].split('.')
        elif word == 'end' and len(namespaces) > 0 and words[wordNum+1] == namespaces[-1]:
            namespaces.pop()
        # deal with defs, theorems, and type classes (don't worry about type classes for now)
        elif ((word == 'def' or word == 'inductive') and words[wordNum-1] != 'private' and words[wordNum-2] != 'private' and 
                not any(words[wordNum+1].startswith(edge_case) for edge_case in ['_root_', '[', '(', '{', '$', '"', '«'])):
            try:
                print(f'fount def {words[wordNum+1]}')
                # for each object name, include the full reference (eg [Namespace].[Object Name])
                rootObj = words[wordNum+1].split(':')[0]
                objectName = '.'.join(namespaces) + f'.{rootObj}' if len(namespaces) > 0 else rootObj
                # get the type, removing redundant parentheses
                objectType = LeanDef(objectName, requiredImports=[importPath]).type
                objects.append(f'{objectName} HAS_TYPE {objectType}')
            except KeyboardInterrupt:
                quit()
            except:
                print(f'could not load def {words[wordNum+1]}')
        elif (word == 'theorem' and words[wordNum-1] != 'private' and words[wordNum-2] != 'private' and 
                not any(words[wordNum+1].startswith(edge_case) for edge_case in ['_root_', '[', '(', '{', '$', '"', '«'])):
            try:
                print(f'fount theorem {words[wordNum+1]}')
                # for each object name, include the full reference (eg [Namespace].[Object Name])
                rootObj = words[wordNum+1].split(':')[0]
                objectName = '.'.join(namespaces) + f'.{rootObj}' if len(namespaces) > 0 else rootObj
                # get the type, removing redundant parentheses
                objectType = LeanTheorem(objectName, requiredImports=[importPath]).prop
                objects.append(f'{objectName} HAS_TYPE {objectType}')
            except KeyboardInterrupt:
                quit()
            except:
                print(f'could not load theorem {words[wordNum+1]}')
    return objects

# this function produces the object list from the passed target files
def generateObjectList (filePaths : list[str]) -> list[list[str]]:
    objects = [] # will store a list of object defs
    for path in filePaths:
        numFiles = 0
        if os.path.isfile(path): # deal with single file
            newObjects = extractLeanObjects(path)
            importPath = newObjects[0]
            for obj in newObjects[1:]:
                objectName, objectType = obj.split(' HAS_TYPE ')
                objects.append([objectName, objectType, importPath])
        else: # deal with all .lean files in directory
            fileList = [] # will store all .lean files in this directory
            for root, dirs, files in os.walk(path):
                for file in files:
                    if file.endswith('.lean'):
                        numFiles += 1
                        fileList.append(os.path.join(root, file))
            for fileNum, filePath in enumerate(fileList):
                print(f'looking at file number {fileNum} out of {numFiles}')
                newObjects = extractLeanObjects(filePath)
                importPath = newObjects[0]
                for obj in newObjects[1:]:
                    objectName, objectType = obj.split(' HAS_TYPE ')
                    objects.append([objectName, objectType, importPath])
    return objects