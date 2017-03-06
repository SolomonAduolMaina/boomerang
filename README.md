After cloning the repo and running make, I ran the Quickstart.src file with the command

./boomerang.native QuickStart.src

as described in the manual on page 10. It ran just fine with the following output:

./boomerang.native QuickStart.src
Test result:
"Hello World"
Test result:
"HELLO WORLD"
Test result:
"Jean Sibelius, 1865-1957, Finnish
Benjamin Britten, 1913-1976, English
Aaron Copland, 1910-1990, American"

So I put failwith statements to track the execution of the program and see what are the most important functions.
I get the following sequence of function calls:

toplevel (line 427 in toplevel.ml)
toplevel' (line 431 in toplevel.ml) is called by toplevel
check (line 385 in toplevel.ml) is called by toplevel'
BRegistry.load_file (line 102 in toplevel.ml) is called by check
go_load (line 255 in bregistry.ml) is called by load_file

Line 255 in bregistry is this line

go_load (fun () -> !interp_file_impl path modl) modl path;

If I put a failwith in this line before !interp_file_impl like this

go_load (fun () -> failwith "I failed here"; !interp_file_impl path modl) modl path;

then the program crashes with output

./boomerang.native QuickStart.src
Uncaught exception Failure("I failed here")

On the other hand if I put the failwith after !interp_file_impl like this

go_load (fun () -> !interp_file_impl path modl; failwith "I failed here") modl path;

then the program crashes with output

./boomerang.native QuickStart.src
Test result:
"Hello World"
Test result:
"HELLO WORLD"
Test result:
"Jean Sibelius, 1865-1957, Finnish
Benjamin Britten, 1913-1976, English
Aaron Copland, 1910-1990, American"
Uncaught exception Failure("I failed here")

So it seems that !inter_file_impl is the function that is doing some work. Now, 
inter_file_impl is implemented on line 225 of bregistry like this:

let interp_file_impl = 
  ref (fun _ _ -> 
         msg "@[Boomerang compiler is not linked! Exiting...@]"; 
         exit 2)

Yet if I run go_load (line 255 in bregistry) like this:

go_load (fun () -> (fun _ _ -> 
         msg "@[Boomerang compiler is not linked! Exiting...@]"; 
         exit 2) path modl) modl path;

then the program crashes with output

./boomerang.native QuickStart.src
Boomerang compiler is not linked! Exiting...

So it seems that the interp_file_impl reference was reassigned somewhere, but I
searched interp_file_impl in the whole project and found no such assignment. So
I don't understand what is happening and why.
-------------------------------------------------------------------------------

I also tried running Boomerang like so as described on page 80 of the manual:

./boomerang.native get QuickStart.comps comps-conc.txt

The program crashes with output 

./boomerang.native get QuickStart.comps comps-conc.txt
get: unexpected run-time
error
string does not match ([ A-Za-z]+.", ".[0-9]{4}."-".[0-9]{4}.", ".[ A-Za-z]+."\n")*.
[ A-Za-z]+.", ".[0-9]{4}."-".[0-9]{4}.", ".[ A-Za-z]+ [Jean Sibelius, 1865-1957, Finnish
Aaron Copland, 1910-1990, American
Benjamin Britten, 1913-1976, English
] AROUND HERE []

Just to save you all the stack details, this exception is being thrown because the 
match_string function in the brx module is failing with the lens Quickstart.comps and the 
string 

Jean Sibelius, 1865-1957, Finnish
Aaron Copland, 1910-1990, American
Benjamin Britten, 1913-1976, English

I haven't debugged the match_string function deep enough to know where exactly the problem lies
so I shall soldier on and try to find the exact problem.
