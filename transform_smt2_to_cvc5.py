import re
import subprocess
import os
import argparse


prime = 21888242871839275222246405745257275088548364400416034343698204186575808495617
def transformar_primo_neg(bigint_str):
        # Convertir la cadena a un entero
    print(bigint_str)
    bigint = int(bigint_str)
        # Restar 2
    resultado = prime - bigint 
    print(resultado)
        # Convertir el resultado de nuevo a cadena
    return str(resultado)



def procesar_texto(texto):
    # Reemplazar números de más de diez cifras por su inverso
    # 1. Aplicar la transformación usando la expresión regular
    texto = re.sub(r'\(- (\d+)\)', lambda x: transformar_primo_neg(x.group(1)), texto)
    texto = re.sub(r" (\d+)", r" (as ff\1 FF0)", texto)
    # Reemplazar cada número negativo de la forma -num por (~ num)
    # 2. Cambiar todos los "FF0" por "Int"
    texto = texto.replace("Int", "FF0")
    texto = texto.replace("Bool", "FF0")
    
    # 3. Cambiar el primer "FF0" (ya no existirá "FF0" en este punto, pero cambiamos el primer "Int") por "ALL"
    texto = texto.replace("QF_FFA)", "QF_FF)\n(define-sort FF0 () (_ FiniteField " + str(prime) +"))", 1)
    
    texto = texto.replace("*","ff.mul")
    texto = texto.replace("+","ff.add")

    #texto = re.sub("21888242871839275222246405745257275088548364400416034343698204186575808495616", "(~ 1)", texto)

    return texto

# Función principal
def main(input,output):

    # Leer el contenido del archivo de salida (o el texto de la ejecución)
    with open(input, "r") as archivo:
        texto = archivo.read()
    
    # Procesar el texto para hacer las transformaciones
    texto_modificado = procesar_texto(texto)

    with open(output, "w") as archivo:
        archivo.write(texto_modificado)
    
    print("Transformación completa.")

    #mover_archivo(output)


# Llamada de ejemplo
if __name__ == "__main__":
    # Crear el parser de argumentos
    parser = argparse.ArgumentParser(description='Script para procesar un archivo .smt2.')
    
    # Agregar el argumento esperado
    parser.add_argument('file', help='Ruta del archivo .smt2')
    
    # Parsear los argumentos de la línea de comandos
    args = parser.parse_args()
    file_path = args.file

    # Verificar que el archivo tiene la extensión .smt2
    if not file_path.endswith('.smt2'):
        raise ValueError("El archivo proporcionado debe tener la extensión .smt2")
    
    # Generar el nombre del archivo de salida
    output = file_path.split('.')[0] + '_transformed.smt2'
    
    # Llamar a la función principal
    main(file_path, output)
