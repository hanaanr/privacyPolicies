import os

file_path = '/home/hanana/Repositories/privacy/Data/release_db.sqlite'
if os.path.isfile(file_path):
    file_size = os.path.getsize(file_path)
    print(f"The file exists and its size is {file_size} bytes.")
else:
    print("The file does not exist.")
