# TFTP client written in Coq and OCaml - university assignment

This is a TFTP client with logic written and verified in Coq and the network communication written in OCaml.

## Usage
```./exec-file -a address -i input_file -o output_file -m mode```
Where:
- ```address``` is the ```getaddrinfo(3)``` compatible address of the server.
- ```input_file``` is the name of the local file when in write mode and the remote file when in read mode.
- ```output_file``` is the name of the remote file when in write mode and the local file when in read mode.
- ```mode``` must be either ```read``` or ```write```. 
  - When it is ```read``` the remote file will be downloaded from the server and saved locally under the name specified in ```output_file```. A file of the same name must not already exist.
  - When it is ```write``` the local file will be uploaded to the server and saved under the name specified in ```output_file```. The local file must already exist.
