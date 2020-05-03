------------------------- MODULE DekkersAlgoNaive2 -------------------------
(* --algorithm Dekkers

variables threadNumber = 1,
p0_count = 0, p1_count = 0, 
p1Critical = FALSE, p2Critical = FALSE;

fair process p0 = 0
begin P0_INIT:
    while p0_count < p0_max do
        await threadNumber = 1;
        \*Critical section
        p0_count := p0_count + 1;
        p1Critical := TRUE;
        RELEASE_P0:
        p1Critical := FALSE;
        threadNumber := 2;
     end while;
end process;

fair process p1 = 1
begin P1_INIT:
     while p1_count < p1_max do
        await threadNumber = 2;
        p1_count := p1_count + 1;
        p2Critical := TRUE;
        RELEASE_P1:
        p2Critical := FALSE;
        threadNumber := 1;
     end while;
end process;

end algorithm; *)

=============================================================================
\* Modification History
\* Last modified Sun May 03 13:21:49 CDT 2020 by shiva
\* Created Sun May 03 13:21:24 CDT 2020 by shiva
