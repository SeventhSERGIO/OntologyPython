import copy
import json


def getOntology(namePath):
    global path
    with open(namePath) as json_file:
        data = json.load(json_file)
        path = namePath
    return data['ontology']

def getPath():
    return path

#Guarda la ontología en un archivo 
def saveOntology(ontology):
    global path
    outData = {"ontology":ontology}
    with open(path, 'w') as outfile:
        json.dump(outData, outfile)

# Verificar si existe una clase con ese nombre nameClase (string) en la ontologia (list)
def isInClass(nameClase, ontology):
    for clase in ontology:
        if clase["clase"] == nameClase:
            return True
    return False

# Obtiene las subclases de una clase nameClase (string) de una ontología (list), de manera recursiva
def _findSubClases(nameClase,ontology):
    i = getIndex(nameClase,ontology) #Obtener el indice de la lista
    onto = ontology[:i]+ontology[i+1:] #Quitar de la lista de busqueda la clase 
    for i,subClase in enumerate(onto):
        if nameClase == subClase['mother']:
            yield subClase
            yield from _findSubClases(subClase['clase'],onto)

# Crea un arreglo de las subclases
def findSubClases(nameClase,ontology):
    subClases = []
    for subClase in _findSubClases(nameClase,ontology):
        subClases.append(subClase)
    return subClases

# Obtener el indice que tiene una clase nameClase (string) dentro de la ontologia ontology (list)
def getIndex(nameClase, ontology):
    
    for i,clase in enumerate(ontology):
        if nameClase == clase['clase']:
            return i
    
    return False

#obtener todas las clases ordenadas por nivel jerarquico en el arbol
def obtenerSupClasesDe(supClase,ontology):
    _supClases = []

    if isInClass(supClase,ontology):
        clase = ontology[getIndex(supClase,ontology)]
        
        for _clase in ontology:
            if _clase["clase"] == clase["mother"]:
                _supClases.append(_clase["clase"])# guarda nombre de clase
                _supClases.extend(obtenerSupClasesDe(_clase["clase"],ontology))

    return _supClases


#ordenar las clases en orden jerarquico, las que son mas especificas hasta abajo
def superClassOfOntology(ontology):
    
    superClase = []
    #optinene el nodo superior de cada clase
    for clase in ontology:
        superClases = obtenerSupClasesDe(clase["clase"],ontology)
        if len(superClases) > 0:
            if len(superClases) == 1:
                superClase.append(superClases[0])
            else:
                superClase.append(superClases[len(superClases) -1])
    valueClass = []
    
    # compara de existir nodos que estan desconectados de la clase superior
    for val in superClase:
        guardado = False
        for i,saveVal in enumerate(valueClass):
            if val == saveVal[0]:
                guardado = True
                valueClass[i][1] = valueClass[i][1] +1
        if guardado is False:
            valueClass.append([val,1])
    # si se da el caso de arriba, elije entre el que tiene mas hijos    
    claseSuperior = ""
    if len(valueClass)  == 1:
        claseSuperior = valueClass[0][0]
    else:
        claseSuperior = valueClass[0][0]
        
        for val in range(1,len(valueClass)):
            if valueClass[val][1] > valueClass[val-1][1]:
                claseSuperior= valueClass[val][0]
    return claseSuperior

def hierarchyTree(ontology):
    #optiene la y guara la clase superior
    claseSuperior = superClassOfOntology(ontology)
    arbolGerarquico =[]
    arbolGerarquico.append([0,claseSuperior])
    #llena el arbol con los niveles inferriores
    arbolGerarquico.extend(getSubclassHierarchy(claseSuperior,1,ontology))
    arbolGerarquico = sorted(arbolGerarquico, key = lambda k : k[0])
    return arbolGerarquico


def getSubclassHierarchy(nombreSuperClase,nivel,ontology):
    
    #subclases totales
    subclassTotal = []
    subclass = []
    #por cada nivel del arbol, agrega sus clases y el nivel que tienen
    for subClass in ontology:
        if subClass["mother"] == nombreSuperClase:
            subclass.append([nivel,subClass["clase"]])
            subclassTotal.append([nivel,subClass["clase"]])
    for className in subclass:
        subclassTotal.extend(getSubclassHierarchy(className[1],nivel + 1,ontology))
            
    return subclassTotal
    
def getPropertiesByInheritance(hierarchyClasses, ontology, properties=None, choosen=None, imp=False):
    
    if properties is None:
        properties = []
    if choosen is None:
        choosen = []
        
    allImplications = []
    consequents = []
    # Por cada clase ordenada por herencia
    for clase in hierarchyClasses:
        tempImplications = []
        # Obtiene el indice de la clase
        indx = getIndex(clase, ontology)
        # Itera por sus propiedades
        for prop in ontology[indx]['properties']:
            # Si la propiedade es diferente a las de implicacion
            if prop['type'] == 'bool' or prop['type'] == 'value':
                # Si la propiedad no esta en las elegidas
                if prop['name'] not in choosen:
                    # Agrega el nombre a las propiedades elegidas
                    choosen.append(prop['name'])
                    # Agrega la propiedad a las propiedades finales
                    properties.append(prop)
            # Si la propiedad es de implicacion crea una lista por clase
            elif prop['type'] == 'imp':
                consequents.append(prop['consequent'])
                tempImplications.append(prop)
                
        # Agrega las listas de propiedades de implicacion
        # (una lista por clase) si existen
        if tempImplications:
            allImplications.append(tempImplications)
    
    # Lista para almacenar los diccionarios de implicacion
    dictsImplications = []
    # Por cada lista de propiedades de implicacion (una por cada clase dentro de la herencia)
    for tempImplication in allImplications:
        implications = dict()
        # Por cada consecuente dentro de las propiedades de implicacion
        for consequent in set(consequents):
            # Si la propiedad no esta definida dentro de las porpiedades elegidas
            if consequent not in choosen:
                # Crea un diccionario donde las propiedades de implicacion tienen el mismo
                # consecunete y estan ordenados por prioridad
                temp = [element for element in tempImplication if element['consequent'] == consequent]
                implications[consequent] = sorted(temp, key=lambda k: k['priority'])
        # Agrega un diccionario por cada clase de herencia
        dictsImplications.append(implications)
        
    # Se obtienen todas las propiedades de tipo valor para inferir en las de implicacion
    dictProperties = {prop['name']: [prop['type'], prop['value'], prop['bool']] 
                      for prop in properties if prop['type']== 'value'}
        
    choosen = []
    # Por cada diccionario de implicacion en cada clase (ordenadas por herencia)
    for implications in dictsImplications:
        # Por cada implicacion (separadas por su concecuente)
        for consequent,implication in implications.items():
            # Si el consecuente aun no se ha elegido (no esta en las propiedades finales)
            if consequent not in choosen:
                # Empieza a verificar las propiedades de implicacion (ordenadas por prioridad)
                for element in implication:
                    # Si el antecedente de la propiedad de implicacion no es una lista, lo hace lista
                    if type(element['antecedent']) is not list:
                        element['antecedent'] = [element['antecedent']]
                    # Verifica que el individuo contenga las propiedades antecedentes
                    if all(antecedent in dictProperties for antecedent in element['antecedent']):
                        # Verifica que las propiedades de antecedentes tengan el mismo valor booleando
                        # que se especifica en la propiedad de implicacion
                        if all(dictProperties[antecedent][2] == value for antecedent,value in zip(element['antecedent'],element['value'])):
                            # Crea una lista con los valores de todos los antecedentes
                            values = [dictProperties[antecedent][1] for antecedent in element['antecedent']]
                            # Si todos los valores en los antecedentes son iguales
                            if len(set(values)) == 1:
                                # Crea una nueva propiedad
                                # type --> mismo tipo que cualquier antecedente
                                # name --> el nombre de la nueva propiedad es el mismo que el consecuente
                                # value --> Elige el primer valor dentro de la lista de valores 
                                # (toda la lista de valores solo debe de contener al mismo)
                                # bool -->  El boolean del consecuente es el mismo que el espeficicado en la ontologia
                                # priority --> es de 0 al ser una propiedad de valor
                                newProperty = {'type': dictProperties[element['antecedent'][0]][0], 
                                               'name': consequent, 
                                               'value': values[0],
                                               'bool': element['value'][-1],
                                               'priority': 0}
                                # Agrega la nueva propiedad a las propiedades finales
                                properties.append(newProperty)
                                # Agrega el nombre de la propiedad a la lista de propiedades elegidas
                                choosen.append(consequent)
                    # Si el consecuente ya se eligio termina de iterar por la lista (ordenada por prioridad)
                    # de implicaciones (ya que todos los consecuentes son los mismos)
                    if consequent in choosen:
                        break
                    elif imp:
                        if len(element['antecedent']) == 1:
                            element['antecedent'] = element['antecedent'][0]
                        properties.append(element)
                        
    return properties

def _directPropertiesOfClass(nameClass, ontology):
    
    # Indice de la clase
    indxClass = getIndex(nameClass, ontology)
    # Obtiene las propiedades de la clase
    classProp = ontology[indxClass]['properties'].copy()
    # Obtiene los nombres de las propiedades elegidas hasta ese momento
    choosen = [prop['name'] for prop in classProp if prop['type'] != 'imp']
    # Se retornan las propiedades completas y las propiedades elegidas
    return classProp, choosen

def getAllPropertiesThatMatch(nameProperty, entities, ontology, propertiesOf, boolean=True):
    
    # Crea un diccionario para almacenar toda la extencion de una propiedad
    valueEntities = dict()
    # Obtiene todas las propiedades de cada individuo
    for entity in entities:
        for prop in propertiesOf(entity,ontology):
            if prop['type'] == 'value':
                if prop['name'] == nameProperty and prop['bool'] == boolean:
                    valueEntities[entity] = prop['value']
            elif prop['type'] == 'bool':
                if prop['name'] == nameProperty and prop['value'] == boolean:
                    valueEntities[entity] = prop['value']
    return valueEntities



def propertiesOfObject(nameObject, ontology):
    
    # Obtiene todas las clases de la ontología (list) a las que pertenece un objeto nameObject (string)
    classes = allObjectClasses(nameObject, ontology)
    # Si no pertenece a ninguna clase mandar mensaje de error
    if not classes: 
        return []
    
    rootClass = superClassOfOntology(ontology)
    
    # Ordena las clases segun el grado de herencia
    classes = [clase['clase'] for clase in findSubClases(rootClass, ontology) 
              if clase['clase'] in classes]
    classes = classes[::-1]
    
    # Clase directa del individuo
    clase = getObjectClass(nameObject,ontology) 
    # Indice de la clase
    indxClass = getIndex(clase, ontology)
    # Indice del individuo en la clase
    indxObject = getIndexObject(nameObject, clase, ontology)
    
    # Obtiene las propiedades del individuo
    indvProp = ontology[indxClass]['individuals'][indxObject]['properties'].copy()
    
    # Obtiene los nombres de las propiedades elegidas hasta ese momento
    choosen = [element['name'] for element in indvProp]
    
    properties = getPropertiesByInheritance(classes, ontology, properties=indvProp, choosen=choosen)
    
    return properties

def propertiesOfClass(nameClass, ontology):
    
    # Obtiene la raiz de la ontologia
    rootClass = superClassOfOntology(ontology)
    # Si la clase raiz es la misma que nameClass
    # returna las propiedades solo de la clase raiz
    if nameClass == rootClass:
        # Obtiene las propiedades de la clase raiz
        classProp, _ = _directPropertiesOfClass(nameClass, ontology)
        # Regresa las propiedades de la clase
        return classProp
    
    # Se obtienen todas la jerarquia de clases a partir de una clase en especifico
    hierarchyClasses = obtenerSupClasesDe(nameClass, ontology)
    # Si la clase no encuentra ninguna superclase entonces la clase 
    # no esta en la ontologia
    if not hierarchyClasses: 
        return []
    
    # Agrgamos la clase a la jerarquia en el indice 0
    hierarchyClasses.insert(0, nameClass)
    
    properties = getPropertiesByInheritance(hierarchyClasses, ontology, imp=True)
    
    return properties

def allObjectClasses(nameObject, ontology):
    clases = []
    for clase in ontology: #Por cada clase de la ontología
         #Si el objeto pertenece a la extensión de la clase
        if nameObject in classExtention(clase['clase'],ontology):
            clases.append(clase['clase']) #El objeto pertenece a la clase
    return clases

def classExtention(nameClase,ontology):
    if not isInClass(nameClase,ontology): #Si no está en 
        return []                         #devolver una lista vacía
    individuals = []
    subClases = findSubClases(nameClase,ontology) #Obtener las sublclases de la clase
    indx = getIndex(nameClase, ontology) #Obtener el indice de la clase
    subClases.append(ontology[indx]) #Agregar la clase a la lista 
    for subClase in subClases: #Por cada clase o subclase
        for individual in subClase['individuals']: #Iterar por sus individuos
            individuals.append(individual['id'])   #Agregarlos a la lista de retorno
    return individuals

def getObjectClass(nameObject, ontology):
    for clase in ontology: #Por cada clase en la lista ontology
        for individual in clase['individuals']: #Iterar en cada uno de los individuos
            if nameObject in individual['id']: #Si se encuentra el objeto
                return clase['clase']  #Devolver la clase
    return [] #De otra forma devuelve una lista vacía

    
#Obtener el indice de un objeto dentro de la lista de individuos de una clase
def getIndexObject(nameObject, nameClass, ontology):
    if not isObjectInClass(nameObject,nameClass,ontology):
        #raise Error('Error: El objeto no esta en la clase.')
        return False
    indexClass = getIndex(nameClass, ontology) #indice de la clase 
    for index, indv in enumerate(ontology[indexClass]['individuals']): #Por cada individuo de la clase
        if indv["id"] == nameObject:
            return index
        
# Verificar si existe un objeto con ese nombre nameObject (string) en la clase nameClass (string)
def isObjectInClass(nameObject,nameClase,ontology):
    classIndex = getIndex(nameClase, ontology)
    for indv in ontology[classIndex]["individuals"]:
        if indv["id"] == nameObject:
            return True
    return False

#buscar clases que tienen declarada la relacion
def clasesConEstaRelacion(nombreRelacion,ontology):
    clasesConEstaRelacion = []
    for clase in ontology:
        for relaciones in clase["relations"]:
            if relaciones["subject"] == nombreRelacion:
                clasesConEstaRelacion.append(clase["clase"])
    return clasesConEstaRelacion
    
def getIndexOfRelation(relationOrigin,clase,ontology):
    index = -1
    for i,relation in enumerate (ontology[getIndex(clase,ontology)]["relations"]):
        if relation["subject"] == relationOrigin:
            index = i
            break
    return index

#clase que obtiene los individuos que tienen un arelacion en especifico
#clase auxiliar del    ejercicio 1) c
def individualWithRelationship(relacionName, ontology):
    indivRel = []
    
    #para cada clase en la ontologia accede a sus individuos
    for idClase, clase in enumerate(ontology):
        for idIndividuo, individuo in enumerate(clase["individuals"]):
            #para cada individuo busca en sus relaciones
            for j, relacion in enumerate(individuo["relations"]):
                if relacion["subject"] == relacionName:
                    #guarda una tupla que relaciones el individuo con el valor de su relacion
                    nombreIndividuo = ontology[idClase]["individuals"][idIndividuo]["id"]
                    valorDeRelacion = ontology[idClase]["individuals"][idIndividuo]["relations"][j]
                    indivRel.append([nombreIndividuo, valorDeRelacion])
    return indivRel

def allRelationshipsOneClass(clase,ontology):
    #optener superClases de la clase
    superClasesDeClase = obtenerSupClasesDe(clase,ontology)
    #optener la clase que se esta buscando
    clase_actual = ontology[ getIndex(clase,ontology) ]
    #almacen de todas las relaciones de esta clase por declaracion directa en la misma
    relacionesDeClase = []
    
    for relInClass in clase_actual["relations"]:
        relacionesDeClase.append(relInClass)
        
    #para cada super clase en forma ascendente, busca
    for claseSup in superClasesDeClase:
        #obtener la clase de la ontologia
        superClase = ontology[ getIndex(claseSup,ontology) ]
        #para cada relacion en la superClase, busca si debo agregar alguna a la subclase
        for relInSupClass in superClase["relations"]:
            #busca en las relaciones que ya tiene la clase
            guardar = True 
            for relClassActual in relacionesDeClase:
                if relClassActual["subject"] == relInSupClass["subject"]:
                    guardar = False
                    break
            
            if guardar is True:
                relacionesDeClase.append(relInSupClass)
    return relacionesDeClase

def getPropertyClassIndex(propertyClass, nameClass, ontology, consequent = None):
    
    indxClass = getIndex(nameClass, ontology) #indice de la clase
    if not indxClass:
        #raise Error('Error: la clase no existe en la ontología')
        return False
    if consequent == None: #Para propiedades tipo bool y value
        for num, prop in enumerate(ontology[indxClass]['properties']): #por cada propiedad
            if prop["name"] == propertyClass: #si coincide con el nombre de la propiedad
                return num #regresar el indice
    else: #Si la propiedad es de implicacion
        for num, prop in enumerate(ontology[indxClass]['properties']): #por cada propiedad
            if prop['type']=='imp': #si la propiedad es de tipo implicacion
                if [prop["antecedent"]] == propertyClass[0] and prop["value"][:-1] == propertyClass[1]: #si coincide con el antecedente y el valor
                    if prop["consequent"] == consequent[0] and prop["value"][-1] == consequent[1]: # Y tambien la consecuencia con su valor
                        return num
    return False #Si no existe la propiedad devuelve False

#Obtener el indice de una propiedad propertyObject (string) de tipo bool o value, de un objeto nameObject
#(string)
def getPropertyObjectIndex(propertyObject, nameObject, ontology):
    nameClass = getObjectClass(nameObject, ontology) #Clase del objeto
    if not nameClass:
        #raise Error('No existe objeto en la ontología')
        return False
    indxClass = getIndex(nameClass, ontology) # Indice de la clase en la ontologia
    indxObject = getIndexObject(nameObject, nameClass, ontology) #Indice del objeto en la clase
    for num, prop in enumerate( ontology[indxClass]['individuals'][indxObject]['properties'] ): #por cada propiedad del objeto
        if prop["name"] == propertyObject:
            return num
    return False

def getRelationClassIndex(subjectRelation, objectRelation, nameClass, ontology):
    if not isInClass(nameClass,ontology): #Si la clase no esta en la ontología
        #raise Error('Error: La Clase no esta en la ontologia.') #Mandar mensaje de error
        return False
    indexClass = getIndex( nameClass, ontology)
    for num, rel in enumerate( ontology[indexClass]['relations']): #por cada relacion en clase
        if rel['subject'] == subjectRelation and rel['object'] == objectRelation: #Si es la relacion específica
            return num
    return False

# objectRelation tiene que ser list
def getRelationObjectIndex(subjectRelation, objectRelation, nameObject, ontology):
    nameClass = getObjectClass(nameObject, ontology) #Clase del objeto
    if not nameClass:
        #raise Error('No existe objeto en la ontología')
        return False
    indxClass = getIndex( nameClass, ontology ) #Indice de clase en ontologia 
    indxObject = getIndexObject( nameObject, nameClass, ontology) # indice de objeto en clase
    for num, rel in enumerate( ontology[indxClass]["individuals"][indxObject]['relations'] ):
        if rel['subject'] == subjectRelation and  rel['object']==objectRelation:
            return num
    return False

def propertyExtension(nameProperty, ontology, *, boolean=True):
    # Obtiene la raiz de la ontologia
    rootClass = superClassOfOntology(ontology)
    # Obtiene todos los individuos de la ontologia
    allIndividuals = classExtention(rootClass,ontology)
    # Obtiene todas las clases de la ontologia
    allClasses = [clase[1] for clase in hierarchyTree(ontology)]
    # Obtiene todos los entidades (individuos-clases) que cumplen con cierta propiedad
    valueIndividuals = getAllPropertiesThatMatch(nameProperty, allIndividuals, ontology, propertiesOf=propertiesOfObject,boolean=boolean)
    valueClasses = getAllPropertiesThatMatch(nameProperty, allClasses, ontology, propertiesOf=propertiesOfClass,boolean=boolean)
    # Une las dos entidades
    return valueIndividuals | valueClasses

def relation_extension(relacion,ontology):
    #clases que tienen la relacion de forma directa
    clases_ = clasesConEstaRelacion(relacion,ontology)
    
    #arbol de gerarquia para ordenar
    tree = hierarchyTree(ontology)
    tree.reverse()
    #ordenar las clases por aparicion gerarquica en la lista
    #clases mas al fondo del arbol con menos gerarquia
    clasesOrdenadas = []
    for class_tree in tree:
        for class_ in clases_:
            if class_ == class_tree[1]:
                clasesOrdenadas.append(class_)
    
    #buscar las subclases de cada clase que tiene la propiedad
    #para extenderle la relacion si no la tiene
    class_subclass = []
   
    for class_ in clasesOrdenadas:
        reg =[]
        reg.append([class_,[]])
        temp = []
        sub = findSubClases(class_,ontology)
        for sub_ in sub:
            temp.append(sub_["clase"])
        reg[0][1].extend(temp)
        class_subclass.extend(reg)
    
    ontologyCopy = copy.deepcopy(ontology)
    
    #heredar la relacion a subclases
    
    for class_root in class_subclass: ## por cada super clase aplica a cada una de sus subclases
        for sub_class in class_root[1]:#por cada subclase  de la superclase
            #verifica que la subclase tenga la relacion
            agregar = True
            # por cada relacion que contiene la sub clase, busca si tiene la relacion buscada
            for relacion_ in ontologyCopy[ getIndex(sub_class,ontologyCopy) ]["relations"]:
                #si la relacion existe marca agregar como falso, si no existe se agregara 
                if relacion_["subject"] == relacion:
                    agregar = False
                    break
            #si la subclase no tiene la relacion, heradala de su superclase
            if agregar is True:        
                # guarda la relcion que se debe de heredar
                rel_herencia = ontologyCopy[ getIndex(class_root[0],ontologyCopy) ]["relations"][getIndexOfRelation(relacion,class_root[0],ontologyCopy)]
                # se agrega la relacion a la subclase
                ontologyCopy[ getIndex(sub_class,ontologyCopy) ]["relations"].append(rel_herencia)
    clasesConRelacion = clasesConEstaRelacion(relacion,ontologyCopy)            
    # hasta aquí regresa las clases que tiene esa propiedad pero no su valor
    #return clasesConRelacion
    #print(clasesConRelacion)
    claseYvalorDeRelacion = []
    for class_ in clasesConRelacion:
        claseYvalorDeRelacion.append ([class_, ontologyCopy[ getIndex(class_,ontologyCopy) ]["relations"][getIndexOfRelation(relacion,class_,ontologyCopy)] ] )
    # hasta aquí existen las clases con su valor
    #return claseYvalorDeRelacion
    #print(claseYvalorDeRelacion)

    #para cada clase, ahora extender la herencia de la relacion a los sujetos de cada clase si es que no la tienen
    for class_ in clasesConRelacion:
        # obtiene la relacion de clase
        relacionDeClase = ontologyCopy[ getIndex(class_,ontologyCopy) ]["relations"][getIndexOfRelation(relacion,class_,ontologyCopy)]
        # obtiene la clase
        claseActual = ontologyCopy[ getIndex(class_,ontologyCopy) ]
        #indice temporal del individuo
        indiceIndividuo = -1
        
        #para cada individuo de la clase heredar la relacion si no la tiene declarada
        for i,individuo in enumerate(claseActual["individuals"]):
            #print(claseActual)
            #print(individuo["id"])
            # indica si es necesario que se agregue la relacion al individuo
            agregarRelacionAIndividuo = True
            for k,relacionesDeIndividuo in enumerate(individuo["relations"]):
                if relacionesDeIndividuo["subject"] == relacion: # ya esta la relacion en el individuo
                    agregarRelacionAIndividuo = False
                    break
                    
            if agregarRelacionAIndividuo is True:
                ontologyCopy[ getIndex(class_,ontologyCopy) ]["individuals"][i]["relations"].append(relacionDeClase)
    
    result = individualWithRelationship(relacion,ontologyCopy)
    return result
    
def allRelationshipsOneObject(objeto,ontology):
    #obtener la clase a la cual pertenece el objeto
    clase = getObjectClass(objeto,ontology)
    #obtener todas las relaciones que tiene directamente o por herencia la clase
    relacionesDeClase = allRelationshipsOneClass(clase,ontology)
    #lista para guardar las relaciones que tiene el objeto localmente
    relacionesDeObjeto = []
    #obtener indice del individuo en su clase
    individuo = getIndexObject(objeto,clase,ontology)
    #obtener las relaciones directas del objeto
    for relacion_ in ontology[getIndex(clase,ontology)]["individuals"][individuo]["relations"]:
        relacionesDeObjeto.append(relacion_)
    
    #verificar de la lista de relacionde herencia por superclase
    #las que no tenga agregarlas
    for rel_class in relacionesDeClase: # para cada relacion de su superClases
        agregar = True
        for rel_ob in relacionesDeObjeto: # busca si esta en las relaciones de objeto si no agregasela
            if rel_class["subject"] == rel_ob["subject"]:
                agregar = False
                break
        
        if agregar is True:
            relacionesDeObjeto.append(rel_class)
    return relacionesDeObjeto

def addObject(individualId,nameClass,ontology):
    if not isInClass(nameClass,ontology): # Si no existe la clase en la ontología: 
        #raise Error('Error: La Clase no esta en la ontologia.') # Mandar mensaje de error
        return False
    individual = {'id':individualId, 'properties':[], 'relations':[]} #Crear diccionario de individuo
    indxClass = getIndex(nameClass, ontology) # Obtener el indice de la clase del nuevo individuo
    ontology[indxClass]['individuals'].append(individual) # Agregar el  nuevo individuo a la lista de individuos
    saveOntology(ontology) #Guardar la ontología
    
def addClass(nameClass,nameSuperClass,ontology):
    if nameSuperClass == None: # Si se quiere agregar una clase raíz
        for clase in ontology: # Encontrar quien era la clase raíz
            if clase["mother"] == None:
                clase["mother"] = nameClass  #Cambiar su madre por la clase agregada
    else:
        if not isInClass(nameSuperClass,ontology): #Si no existe la clase en la ontología
            #raise Error('Error: La Clase no esta en la ontologia.') #Mandar mensaje de error
            return False
    #Crear diccionario para la clase
    newClass = {'clase':nameClass, 
                'mother':nameSuperClass,
                'properties':[], 
                'relations':[], 
                'individuals':[]}
    ontology.append(newClass) # Agregar la clase a la ontología 
    saveOntology(ontology) # Guardar la ontología
    
def addClassProperty(nameClass, propertyName, propertyValue, ontology, *, boolean=True, priority=None):
    if not isInClass(nameClass,ontology): #Si la clase no esta en la ontología
        return False
    indxClass = getIndex(nameClass, ontology) #Indice de la clase 
    if priority is not None: #Si hay prioridad la propiedad es de implicación
        newProperty = {'type':'imp',
                       'antecedent':propertyName[0],
                       'consequent':propertyValue[0],
                       'value': propertyName[1] + [propertyValue[1]],
                       'priority':priority}
    # De otra forma la propiedad puede ser boleana o de valor
    elif type(propertyName) is not list and type(propertyValue) is not list: 
        if type(propertyValue) is bool:
            newProperty = {'type':"bool", #Solo se diferencian por su tipo
                           'name':propertyName,
                           'value':propertyValue, 
                           'priority':0} #La prioridad por default es 0
        else:
            newProperty = {'type':"value", #Solo se diferencian por su tipo
                           'name':propertyName,
                           'value':propertyValue,
                           'bool': boolean,
                           'priority':0} #La prioridad por default es 0
    else:
        return False
        
    ontology[indxClass]['properties'].append(newProperty) #Agregar a la lista de propiedades de la clase
    saveOntology(ontology) #Guardar ontología
    
def addObjectProperty(nameObject, propertyName, propertyValue, ontology, *, boolean=True):
    clase = getObjectClass(nameObject,ontology) #Clase directa del individuo
    if not clase: # Si no pertenece a ninguna clase mandar mensaje de error
        return False
    indxClass = getIndex(clase, ontology) #Indice de la clase
    
    #Nueva propiedad para el individuo: colocar nombre del atributo y su valor
    if type(propertyValue) is bool:
        newProperty = {'type':"bool", #Solo se diferencian por su tipo
                       'name':propertyName,
                       'value':propertyValue, 
                       'priority':0} #La prioridad por default es 0
    else:
        newProperty = {'type':"value", #Solo se diferencian por su tipo
                       'name':propertyName,
                       'value':propertyValue,
                       'bool': boolean,
                       'priority':0} #La prioridad por default es 0
        
    indxObject = getIndexObject(nameObject, clase, ontology) #indice del individuo en la clase
    ontology[indxClass]["individuals"][indxObject]["properties"].append(newProperty)#Agregar a la lista de propiedades del individuo
    saveOntology(ontology) #Guardar ontología
    
def addClassRelation(nameClass, newRelation, otherClasses_Objects, ontology, value=True):
    
    if not isInClass(nameClass, ontology):
        #raise Error('Error: La clase no esta en la ontologia.')
        return False
    
    if type(otherClasses_Objects) is not list:
        otherClasses_Objects = [otherClasses_Objects]
    
    for element in otherClasses_Objects:
        if not isInClass(element, ontology):
            if not getObjectClass(element,ontology):
                ##raise Error('Error: La clase o individuo para asignar esa relacion no esta en la ontologia.')
                return False
            
    objects = otherClasses_Objects[0] if len(otherClasses_Objects) == 1 else otherClasses_Objects
    
    newRelation = {'type':'value',
                   'subject': newRelation,
                   'object': objects,
                   'value': value,
                   'priority': 0}
    
    # Indice de la clase
    indxClass = getIndex(nameClass, ontology)
    
    ontology[indxClass]['relations'].append(newRelation)
    saveOntology(ontology)
    
def addObjectRelation(nameObject, newRelation, otherClasses_Objects, ontology, value=True):
    
    # Clase directa del individuo
    clase = getObjectClass(nameObject,ontology) 
    # Si no pertenece a ninguna clase mandar mensaje de error
    if not clase: 
        #raise Error('Error: El individuo no esta en la ontologia.')
        return False
        
    if type(otherClasses_Objects) is not list:
        otherClasses_Objects = [otherClasses_Objects]
    
    for element in otherClasses_Objects:
        if not isInClass(element, ontology):
            if not getObjectClass(element,ontology):
                #raise Error('Error: La clase o individuo para asignar esa relacion no esta en la ontologia.')
                return False
    
    objects = otherClasses_Objects[0] if len(otherClasses_Objects) == 1 else otherClasses_Objects
    
    newRelation = {'type':'value',
                   'subject': newRelation,
                   'object': objects,
                   'value': value,
                   'priority': 0}
    
    # Indice de la clase
    indxClass = getIndex(clase, ontology)
    # Indice del individuo en la clase
    indxObject = getIndexObject(nameObject, clase, ontology)
    
    ontology[indxClass]['individuals'][indxObject]['relations'].append(newRelation)
    saveOntology(ontology)
    
def removeClass(nameClass, ontology):
    
    indxClass = getIndex(nameClass, ontology) #Indice de la clase 
    if not isInClass(nameClass,ontology): # Si no existe la clase en la ontología: 
        #raise Error('Error: La Clase no esta en la ontologia.') # Mandar mensaje de error
        return False
    ind = ontology[indxClass]['individuals']
    mother = ontology[indxClass]['mother']
    ontology.pop(indxClass) #Eliminar la clase de la ontologia
    for clase in ontology:
        if clase['mother'] == nameClass:
            clase['mother'] = mother
    indxMother = getIndex(mother, ontology) #Indice de la clase 
    ontology[indxMother]['individuals'].extend(ind)
    saveOntology(ontology) #Guardar ontología
    updateRelations(nameClass,ontology)
    
def removeObject(nameObject, ontology):
    nameClass = getObjectClass(nameObject,ontology) #Clase del objeto
    if not nameClass:
        #raise Error('Error: El objeto no existe.')
        return False
    indexClass = getIndex(nameClass, ontology) #Indice de la clase
    indexObject = getIndexObject(nameObject, nameClass, ontology) #Indice del objeto
    ontology[indexClass]["individuals"].pop(indexObject) #Eliminar objeto 
    saveOntology(ontology) #Guardar ontología
    
def removeClassProperty(propertyClass, nameClass, ontology, consequent = None):
    indxProp = getPropertyClassIndex(propertyClass, nameClass, ontology, consequent) #indice de la propiedad
    indxClass = getIndex(nameClass, ontology) #indice de la clase
    ontology[indxClass]['properties'].pop(indxProp) #Eliminar propiedad
    saveOntology(ontology) #Guardar ontología
    
def removeObjectProperty(propertyObject, nameObject, ontology):
    indxProperty = getPropertyObjectIndex(propertyObject, nameObject, ontology)
    #Falta poner caso en donde no exista la propiedad en el objeto
    nameClass = getObjectClass(nameObject, ontology) #Clase del objeto
    indxClass = getIndex(nameClass, ontology) # indice de clase en la ontologia
    indxObject = getIndexObject(nameObject, nameClass, ontology) #Indice del objeto en la clase
    ontology[indxClass]['individuals'][indxObject]['properties'].pop(indxProperty) #eliminar propiedad
    saveOntology(ontology) #Guardar ontología
    
def removeClassRelation(subjectRelation, objectRelation, nameClass, ontology):
    indxCR = getRelationClassIndex(subjectRelation, objectRelation, nameClass, ontology) #indice de la relacion en clase
    if not indxCR:
        return False
    indxClass = getIndex(nameClass,ontology) #indice de la clase en la ontologia}
    print(indxClass)
    print(indxCR)
    # if not indxClass:
    #     return False
    # else:
    #     ontology[indxClass]['relations'].pop(indxCR) #Eliminar relacion
    #     saveOntology(ontology) #Guardar ontología
    
def removeObjectRelation(subjectRelation, objectRelation, nameObject, ontology):
    indxRO = getRelationObjectIndex(subjectRelation, objectRelation, nameObject, ontology)
    nameClass = getObjectClass(nameObject, ontology)
    indxClass = getIndex(nameClass, ontology) #Indice de clase en ontologia 
    indxObj = getIndexObject( nameObject, nameClass, ontology) # indice de objeto en clase
    ontology[indxClass]['individuals'][indxObj]['relations'].pop(indxRO) #Eliminar relacion de objeto
    saveOntology(ontology) #Guardar ontología
    
def changeNameClass(nameClass,newNameClass,ontology):
    indexClass = getIndex(nameClass, ontology) #Indice de la clase
    if not isInClass(nameClass,ontology): # Si no existe la clase en la ontología: 
        #raise Error('Error: La Clase no esta en la ontologia.') # Mandar mensaje de error
        return False
    ontology[indexClass]["clase"] = newNameClass #Cambiar el nombre de la clase
    saveOntology(ontology) #Guardar ontología
    
def changeNameObject(nameObject,newNameObject,ontology):
    nameClass = getObjectClass(nameObject,ontology) #Clase del objeto
    if not nameClass: # Si no existe la clase en la ontolgia
        #raise Error('Error: El objeto no está en la ontología.')
        return False
    indexClass = getIndex(nameClass, ontology) #Indice de la clase
    indexObject = getIndexObject(nameObject, nameClass, ontology) #Indice del objeto
    ontology[indexClass]["individuals"][indexObject]["id"] = newNameObject #Cambiar el nombre del objeto
    saveOntology(ontology) #Guardar ontología
    updateNameRelations(nameObject,newNameObject,ontology)
    
def change_value_class_property(nameClass,propertyName,propertyValue,ontology,*,boolean = True, priority = None):
    if not isInClass(nameClass,ontology): #Si la clase no esta en la ontología
        #raise Error('Error: La Clase no esta en la ontologia.') #Mandar mensaje de error
        return False
    indxClass = getIndex(nameClass, ontology) #Indice de la clase 
    #Si hay prioridad la propiedad es de implicación
    if priority is not None and type(propertyName) is list and type(propertyValue) is list: 
        newProperty = {'type':'imp',
                       'antecedent':propertyName[0],
                       'consequent':propertyValue[0],
                       'value': propertyName[1] + [propertyValue[1]],
                       'priority':priority}
    # De otra forma la propiedad puede ser boleana o de valor
    elif type(propertyName) is not list and type(propertyValue) is not list: 
        if type(propertyValue) is bool:
            newProperty = {'type':"bool", #Solo se diferencian por su tipo
                           'name':propertyName,
                           'value':propertyValue, 
                           'priority':0} #La prioridad por default es 0
        else:
            newProperty = {'type':"value", #Solo se diferencian por su tipo
                           'name':propertyName,
                           'value':propertyValue,
                           'bool': boolean,
                           'priority':0} #La prioridad por default es 0
    else:
        #raise Error('Error: Si es propiedad de implicacion agregar prioridad.')
        return False
        
    typePropertyNameField=""
    propertyName_=""
    if newProperty["type"] == "imp":
        if len(newProperty["antecedent"]) == 1:
            propertyName_= newProperty["antecedent"][0]
        else:
            propertyName_= newProperty["antecedent"]
    else:    
        propertyName_= newProperty["name"]
    
    #busca la propiedad en la clase
    confirmacion = False
    for i,property_ in enumerate(ontology[indxClass]['properties']):
        #identificar como se llama la llave con la que buscar el identificado de la propiedad
        if property_["type"] == "imp":     
            typePropertyNameField = "antecedent"
        else:
            typePropertyNameField = "name"
        #encuentra la propiedad actual con ese nombre
        if property_[typePropertyNameField] == propertyName_: 
            if property_["type"] == newProperty["type"]:  #si las estrcuturas de propiedad son las mismas
                ontology[indxClass]['properties'][i] = newProperty
                saveOntology(ontology) #Guardar ontología solo cuando hubo cambios
                confirmacion = True
            else:
                print("No son del mismo tipo")
                

    return confirmacion

def change_value_object_property(nameObject,propertyName,propertyValue,ontology,*,boolean=True):
    class_name = getObjectClass(nameObject,ontology)
    object_index = getIndexObject(nameObject,class_name,ontology)
    
    if type(propertyValue) is bool:
        newProperty = {'type':"bool", #Solo se diferencian por su tipo
                       'name':propertyName,
                       'value':propertyValue, 
                       'priority':0} #La prioridad por default es 0
    else:
        newProperty = {'type':"value", #Solo se diferencian por su tipo
                       'name':propertyName,
                       'value':propertyValue,
                       'bool': boolean,
                       'priority':0} #La prioridad por default es 0
        
    #busca la propiedad que va actualizar y aplica el cambio
    confirmacion = False
    for i,property_ in enumerate(ontology[getIndex(class_name,ontology)]["individuals"][object_index]["properties"]):
        if property_["name"] == propertyName :
            if property_["type"] == newProperty["type"]:
                ontology[getIndex(class_name,ontology)]["individuals"][object_index]["properties"][i] = newProperty
                confirmacion = True
                
            else:
                print("No son del mismo tipo")
    return confirmacion
    saveOntology(ontology) #Guardar ontología
    
def changeClassRelation(nameClass, nameRelation, newClasses_Objects, ontology):
    
    if not isInClass(nameClass, ontology):
        ##raise Error('Error: La clase no esta en la ontologia.')
        return False
        
    if type(newClasses_Objects) is not list:
        newClasses_Objects = [newClasses_Objects]
    
    for element in newClasses_Objects:
        if not isInClass(element, ontology):
            if not getObjectClass(element,ontology):
                #raise Error('Error: La clase o individuo para asignar esa relacion no esta en la ontologia.')
                return False
        
    # Indice de la clase
    indxClass = getIndex(nameClass, ontology)
    
    for relation in ontology[indxClass]['relations']:
        if relation['subject'] == nameRelation:
            if len(newClasses_Objects) == 1:
                relation['object'] = newClasses_Objects[0]
            else:
                relation['object'] = newClasses_Objects
            saveOntology(ontology)
            return
    
    #raise Error('Error: La relacion no esta en la clase de la ontologia.')
    return False

def changeObjectRelation(nameObject, nameRelation, newClasses_Objects, ontology):
    # Clase directa del individuo
    clase = getObjectClass(nameObject,ontology) 
    # Si no pertenece a ninguna clase mandar mensaje de error
    if not clase: 
        #raise Error('Error: El individuo no esta en la ontologia.')
        return False
    
    # Si el individuo para asignar la relacion no existe manda error
    if type(newClasses_Objects) is not list:
        newClasses_Objects = [newClasses_Objects]
        
    for element in newClasses_Objects:
        if not isInClass(element, ontology):
            if not getObjectClass(element,ontology):
                #raise Error('Error: La clase o individuo para asignar esa relacion no esta en la ontologia.')
                return False
            
    # Indice de la clase
    indxClass = getIndex(clase, ontology)
    # Indice del individuo en la clase
    indxObject = getIndexObject(nameObject, clase, ontology)
    
    for relation in ontology[indxClass]['individuals'][indxObject]['relations']:
        if relation['subject'] == nameRelation:
            if len(newClasses_Objects) == 1:
                relation['object'] = newClasses_Objects[0]
            else:
                relation['object'] = newClasses_Objects
            saveOntology(ontology) #Guardar ontología
            return 
        
    #raise Error('Error: La relacion no esta en el individuo de la ontologia.')
    return False


def updateRelations(name,ontology):
    for i, clase in enumerate(ontology):
        for j, relacion in enumerate(clase["relations"]):
            if relacion["object"] == name:
                ontology[i]["relations"].pop(j)
        for k, individuo in enumerate(clase["individuals"]):
            for h, relacion in enumerate(individuo["relations"]):
                if relacion["object"] == name:
                    ontology[i]["individuals"][k]["relations"].pop(h)   
    saveOntology(ontology)     
    
    
    
def updateNameRelations(name,newName,ontology):
    for i, clase in enumerate(ontology):
        for j, relacion in enumerate(clase["relations"]):
            if relacion["object"] == name:
                ontology[i]["relations"][j]["object"] = newName
        for k, individuo in enumerate(clase["individuals"]):
            for h, relacion in enumerate(individuo["relations"]):
                if relacion["object"] == name:
                    ontology[i]["individuals"][k]["relations"][h]["object"] = newName
    saveOntology(ontology)