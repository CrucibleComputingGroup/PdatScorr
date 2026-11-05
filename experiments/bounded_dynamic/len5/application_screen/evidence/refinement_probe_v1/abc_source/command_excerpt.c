int Abc_CommandAbc9GlaRefine( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    extern int Gia_ManNewRefine( Gia_Man_t * p, Abc_Cex_t * pCex, int iFrameStart, int iFrameExtra, int fVerbose );
    int iFrameStart = 0;
    int iFrameExtra = 0;
    int fMinCut = 1;
    int c, fVerbose = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "FGmvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'F':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-F\" should be followed by an integer.\n" );
                goto usage;
            }
            iFrameStart = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iFrameStart < 0 )
                goto usage;
            break;
        case 'G':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-G\" should be followed by an integer.\n" );
                goto usage;
            }
            iFrameExtra = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( iFrameExtra < 0 )
                goto usage;
            break;
        case 'm':
            fMinCut ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pAbc->pGia == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9GlaRefine(): There is no AIG.\n" );
        return 1;
    }
    if ( Gia_ManRegNum(pAbc->pGia) == 0 )
    {
        Abc_Print( -1, "The network is combinational.\n" );
        return 0;
    }
    if ( pAbc->pCex == NULL )
    {
        Abc_Print( -1, "Abc_CommandAbc9GlaRefine(): There is no counter-example.\n" );
        return 1;
    }
    pAbc->Status = Gia_ManNewRefine( pAbc->pGia, pAbc->pCex, iFrameStart, iFrameExtra, fVerbose );
    Abc_FrameReplaceCex( pAbc, &pAbc->pGia->pCexSeq );
    return 0;

usage:
    Abc_Print( -2, "usage: &gla_refine [-FG num] [-vh]\n" );
    Abc_Print( -2, "\t         refines the pre-computed gate map using the counter-example\n" );
    Abc_Print( -2, "\t-F num : starting timeframe for suffix refinement [default = %d]\n", iFrameStart );
    Abc_Print( -2, "\t-G num : the number of additional timeframes to try [default = %d]\n", iFrameExtra );
//    Abc_Print( -2, "\t-m     : toggle using min-cut to derive the refinements [default = %s]\n", fMinCut? "yes": "no" );
    Abc_Print( -2, "\t-v     : toggle printing verbose information [default = %s]\n", fVerbose? "yes": "no" );
    Abc_Print( -2, "\t-h     : print the command usage\n");
    return 1;
}

