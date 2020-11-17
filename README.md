# pvt-2020-assignments
Code for the Program Verification Techniques (2IMP10) assignments

# NuSMV commands
`NuSMV -h` gives you a list of all options

```bash
NuSMV -int <file.smv> # starts NuSMV in interactive mode
go
pick_state -r # (randomly pick a state)
print_current_state -v # (verbose)
simulate -r -k <N> # (simulate behaviour by randomly performing N steps)
show_traces -v
quit
```
