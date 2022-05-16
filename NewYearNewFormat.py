### Script to convert benchmark files using the old (<= 2021) format into the new one (2022)
### Warning : SLOW
import os
import glob
import gzip
import shutil

########### MUST EDIT THESE 3 PATHS ##############
ogPath = "./benchmark_files/"    # path for the current files with the old format
newPath = "./2022_files/"        # path for the newly created files using the new format
tempPath = "./temp/"             # path to temporarily store uncompressed files
##################################################


for path in glob.glob(ogPath + "*.gz"):
    print(path)

    # Creating the uncompressed file
    uncompressedFile = os.path.basename(path)
    with gzip.open(path, 'rb') as compressedFile:
        with open(tempPath + uncompressedFile, 'wb') as uncompressedPath:
	        shutil.copyfileobj(compressedFile, uncompressedPath)

    uncompressedPath = tempPath + uncompressedFile
    fileIN = open(uncompressedPath, "rt")
    
    print(tempPath + uncompressedFile)
    # Find the top to replace it, and remove the line starting in p
    top = 0
    for line in fileIN:
        if line.startswith('p'):
            try:
                top = line.split().pop(4)
                print(top)
            except Exception as e:
                print(e)
                continue     
            lineToRemove = line
            break

    if (top == 0): 
        print("ERROR : " + path + " is a bottom")
        print("Press any button to continue execution")
        input()
        continue


    # quick 'n dirty way to reset the line counter (may the lord have mercy)
    fileIN.close()
    fileIN = open(uncompressedPath, "rt")

    fileOUT = gzip.open(newPath + uncompressedFile, "wb+")

    # Do the actual work
    for line in fileIN:
        if (line == lineToRemove):
            continue
        if (line.startswith(top)):
            line = line.split()
            line[0] = '\nh'
            fileOUT.write(' '.join(line).encode())
        else:
            fileOUT.write(line.encode())

    fileIN.close()
    fileOUT.close()

    os.remove(uncompressedPath) # Remove temp file





