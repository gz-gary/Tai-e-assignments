import os
import shutil

def find_file_by_name(root_folder, file_name):
    for root, dirs, files in os.walk(root_folder):
        if file_name in files:
            return os.path.join(root, file_name)
    return None

# Define the root folder to start the search and the file name to search for
root_folder = '../src'
destination_folder = './'

file_names = ['Solver.java', 'TaintAnalysiss.java']
for file_name in file_names:
    # Find the file
    source_file = find_file_by_name(root_folder, file_name)
    if source_file:
        # Copy the file
        shutil.copy(source_file, destination_folder)
        print(f'File {file_name} copied to {destination_folder}')
    else:
        print(f'File {file_name} not found in {root_folder}')