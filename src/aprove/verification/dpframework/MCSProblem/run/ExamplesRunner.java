package aprove.verification.dpframework.MCSProblem.run;

import java.io.*;
import java.util.*;

import aprove.verification.dpframework.MCSProblem.mcnp.*;

public class ExamplesRunner {

    public static final long PROGRAM_TIMEOUT = Long.MAX_VALUE; //5*60*60*1000;
    public static final long SCC_TIMEOUT = Long.MAX_VALUE; //150*60*1000;
    public static final boolean RANK_FUNC_TO_FILE=false;

    public static String printTime(long time) {
        String reportTime = time/(60*60*1000)+":"+(time/(60*1000))%60+":"+(time/1000)%60+":"+time % 1000;
        return reportTime;
    }

    public static void testFolder(String dir, boolean verify) {
        Config.silenceMode();
        if (!dir.endsWith("\\")) {
            dir=dir+"\\";
        }


        Hashtable<String,Integer> orderingsCount = new Hashtable<String,Integer>();
        for (String ord : Config.GRAPHS_ORDERING_TYPES) {
            orderingsCount.put(ord, 0);
        }

        File dirFile=new File(dir);
        if (!dirFile.exists() || !dirFile.isDirectory()) {
            throw new RuntimeException("Directory "+dir+" does not esist.");
        }

        int total = 0;
        int succeded = 0;
        int failed = 0;
        int timeouts = 0;
        int errors = 0;

        long maxTime = 0;
        String maxTimeExample = null;

        long totalTime = 0;

        int totalSCCs = 0;
        int succededSCCs = 0;
        int failedSCCs = 0;
        int timeoutsSCCs = 0;
        int errorsSCCs = 0;

        File[] files = dirFile.listFiles();
        for (int i=0; i<files.length; i++) {
            String fileName= files[i].getName();
//            System.out.println(fileName);
            if (!fileName.endsWith(".mc1") && !fileName.endsWith(".mc2")) {
                continue;
            }

            total++;

            int indexOfDot = fileName.indexOf(".");
            String exampleId = fileName.substring(0,indexOfDot);

            // System.out.println("Processing "+fileName+":");
            Program currentProg = Program.create(files[i].getAbsolutePath());
            List<Program> sccPrograms = currentProg.getSCCPrograms();


            long timeLeft = ExamplesRunner.PROGRAM_TIMEOUT;
            int progTotal = sccPrograms.size();
            int progSucceded = 0;
            int progFailed = 0;
            int progTimeouts = 0;
            int progErrors = 0;

            long progTotalTime = 0;


            int sccNum = 0;
            for (Iterator<Program> sccIt=sccPrograms.iterator(); sccIt.hasNext() && timeLeft>0; ) {
                Program sccProg = sccIt.next();
                sccNum++;

                try {
                    RunnerThread runnerThread = new RunnerThread(sccProg,true);
                    runnerThread.start();
                    runnerThread.join(Math.max(0,Math.min(ExamplesRunner.SCC_TIMEOUT,timeLeft)));
                    // System.out.println(timeLeft);
                    if (runnerThread.isAlive()) {
                        //System.out.println("TIMEOUTTTTTT");
//                        System.out.println(fileName+"\t"+exampleId+"\tTIMEOUT\tUNKNOWN\tUNKNOWN\t"+runnerThread.getBiggestMCGSize());
                        progTimeouts++;
                        runnerThread.interrupt();
                        progTotalTime+=(Math.min(ExamplesRunner.SCC_TIMEOUT,timeLeft));
                        timeLeft-=(Math.min(ExamplesRunner.SCC_TIMEOUT,timeLeft));
                        continue;
                    } else if (runnerThread.isErrorOccured()) {
                        progErrors++;
                        runnerThread.getEerror().printStackTrace();
                        timeLeft-=runnerThread.getTime();
                        progTotalTime+=runnerThread.getTime();
                        continue;
                    }

                    long time = runnerThread.getTime();
                    timeLeft-=time;

                    List<MCGraphMapping> rankingFunction = runnerThread.getRankingFunction();
                    progTotalTime+=time;
                    if (rankingFunction!=null) {
                        progSucceded++;
                        for (MCGraphMapping map : rankingFunction) {
                            if (map instanceof LevelMapping) {
                                String ord = ((LevelMapping)map).getType();
                                orderingsCount.put(ord, orderingsCount.get(ord)+1);
                            }
                        }
                    } else {
                        progFailed++;
                    }
                    //write to file SCC's graphs IDs list a nd ranking function  if succeeded
                    if (ExamplesRunner.RANK_FUNC_TO_FILE) {
                        String res="yes";
                        if (rankingFunction==null) {
                            res="no";
                        }
                        BufferedWriter output = new BufferedWriter(new FileWriter(dir+fileName+"-scc_"+sccNum+"."+res+".rf"));
                        List<String> mcgsIDs = new ArrayList<String>();
                        for (Iterator<MCGraph> it=sccProg.getInitialMCGraphs().iterator(); it.hasNext(); ) {
                            mcgsIDs.add(it.next().getID());
                        }
                        output.write(mcgsIDs+"\n");
                        if (rankingFunction!=null) {
                            for (Iterator<MCGraphMapping> it=rankingFunction.iterator(); it.hasNext(); ) {
                                MCGraphMapping map=it.next();
                                if (map instanceof LevelMapping) {
                                    output.write(map+"\n");
                                }
                            }
                            //output.write(rankingFunction+"\n");
                        }
                        output.close();
                    }
                } catch (Throwable e) {
                    progErrors++;
                    System.out.println(fileName+"\tFAILED");
                    System.err.println("Exception accured in:"+fileName);
                    e.printStackTrace();
                }
                System.gc();
            }

            totalSCCs += progTotal;
            succededSCCs += progSucceded;
            failedSCCs += progFailed;
            timeoutsSCCs += progTimeouts;
            errorsSCCs += progErrors;

            totalTime+=progTotalTime;
            if (progTotalTime>maxTime) {
                maxTime=progTotalTime;
                maxTimeExample = fileName;
            }
            String biggestMCGSize = "0";
            if (currentProg.getBiggestMCG()!=null) {
                biggestMCGSize=""+currentProg.getBiggestMCG().getNumOfEdges();
            }
            String biggestMCGSizeNodes = "0";
            if (currentProg.getBiggestMCGNodes()!=null) {
                biggestMCGSizeNodes=""+currentProg.getBiggestMCGNodes().getNumOfNodes();
            }
            String biggestMCGSizeNodesPerProgramPoint = "0";
            if (currentProg.getBiggestMCGNodesPerProgramPoint()!=null) {
                biggestMCGSizeNodesPerProgramPoint=""+currentProg.getBiggestMCGNodesPerProgramPoint().getNumOfNodesPerProgramPoint();
            }
            if (progSucceded==progTotal) {
                succeded++;
                System.out.println(exampleId+"\tYES\t"+progSucceded+"\\"+progTotal+"\t"+ExamplesRunner.printTime(progTotalTime)+"\t"+progTotalTime+"\t"+biggestMCGSize+"\t"+biggestMCGSizeNodes+"\t"+biggestMCGSizeNodesPerProgramPoint);
            } else if (progSucceded+progFailed==progTotal) {
                failed++;
                System.out.println(exampleId+"\tNO\t"+progSucceded+"\\"+progTotal+"\t"+ExamplesRunner.printTime(progTotalTime)+"\t"+progTotalTime+"\t"+biggestMCGSize+"\t"+biggestMCGSizeNodes+"\t"+biggestMCGSizeNodesPerProgramPoint);
            } else {
                if (progTimeouts>0) {
                    timeouts++;
                }
                if (progErrors>0) {
                    errors++;
                }
                System.out.println(exampleId+"\tTIMEOUT/ERROR\t"+progSucceded+"\\"+progTotal+" (Failed:"+progFailed+",Timeouts:"+progTimeouts+",Errors:"+progErrors+")"+"\t"+ExamplesRunner.printTime(progTotalTime)+"\t"+progTotalTime+"\t"+biggestMCGSize+"\t"+biggestMCGSizeNodes+"\t"+biggestMCGSizeNodesPerProgramPoint);
            }
        }

        System.out.println("Succeeded: "+succeded);
        System.out.println("Failed: "+failed);
        System.out.println("Timeouts: "+timeouts);
        System.out.println("Errors/Exceptions: "+errors);
        System.out.println("Total: "+total);
        System.out.println("Total time: "+ExamplesRunner.printTime(totalTime));
        System.out.println("Average time: "+ExamplesRunner.printTime(totalTime/total));
        System.out.println("The longest example is "+maxTimeExample + " took "+ExamplesRunner.printTime(maxTime)+".");

        System.out.println("SCCs succeeded: "+succededSCCs);
        System.out.println("SCCs failed: "+failedSCCs);
        System.out.println("SCCs total: "+totalSCCs);

        // delete files in temp dir
        File currentDir=new File("TMP");
        for (File f1 : currentDir.listFiles()) {
            if (f1.getName().startsWith("mcnp")) {
                f1.delete();
            }
        }

        // print orderings usage statistics
        for (String ord : Config.GRAPHS_ORDERING_TYPES) {
            System.out.println(ord+": "+orderingsCount.get(ord));
        }

    }

    public static void testFolder(String dir) {
        ExamplesRunner.testFolder(dir,false);
    }

    public static void main(String[] args)
    {
        String folder = null;

        folder = "E:\\MSc\\ManyExamples\\clpq-aprove20110107\\mc\\";
        folder = "O:\\teza\\ManyExamples\\CarstenDumpsPEed_mc\\";
        folder="E:\\MSc\\ManyExamples\\CarstenDumpsPEed_PEed_mc";
        folder="E:\\MSc\\ManyExamples\\Carsten3\\CarstenDumpsPEed_mc";
        folder="E:\\MSc\\ManyExamples\\Samir_PE2\\clpqPE2_mc";
        folder="E:\\MSc\\ManyExamples\\CarstenV4\\CarstenV4PE2_mc\\";

        folder="E:\\MSc\\ManyExamples\\Current_mc\\";

//        folder="D:\\clpqPE2\\MCGraphs\\";
        folder="E:\\MSc\\ManyExamples\\MCGraphs_PE\\";

        folder = "C:\\Users\\Igor\\Documents\\My Dropbox\\MCGraphs\\BookExamples\\";

        folder = "C:\\Users\\Igor\\Documents\\My Dropbox\\MCGraphs\\Samir\\";
//        folder = "D:\\dropbox\\My Dropbox\\MCGraphs\\Samir\\";
//        folder = "D:\\dropbox\\My Dropbox\\MCGraphs\\Carsten\\";
//        folder = "D:\\dropbox\\My Dropbox\\MCGraphs\\Fred\\";
//
//        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\check2\\mc_samir_b";
//        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\mc_samir_1.2.2011\\";
//        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\mc_carsten_1.2.2011\\";
        folder = "D:\\dropbox\\My Dropbox\\MCGraphs\\Samir\\";
        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\pe_samir_4.2.2011\\";
//        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\pe_carsten_4.2.2011\\";
        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\pe_fred_4.2.2011\\";

        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\pe4_samir_4.2.2011\\";
//        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\pe4_carsten_4.2.2011\\";
//        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\pe4_fred_4.2.2011\\";
//
        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\pe2_samir_6.2.2011\\";
        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\pe2_carsten_6.2.2011\\";
//        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\pe2_fred_6.2.2011\\";

        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\pe2_pruned1_samir_7.2.2011\\";
//        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\pe2_pruned1_carsten_7.2.2011\\";
        folder="D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\pe2_pruned1_fred_7.2.2011\\";


        folder="C:\\Users\\Igor\\Documents\\My Dropbox\\MCExamples\\Examples\\pe_samir.8.2.2011\\";
        folder="C:\\Users\\Igor\\Documents\\My Dropbox\\MCExamples\\Examples\\pe_carsten.8.2.2011\\";
        folder="C:\\Users\\Igor\\Documents\\My Dropbox\\MCExamples\\Examples\\pe_fred.8.2.2011\\";
//      folder = "D:\\dropbox\\My Dropbox\\MCExamples\\Examples\\pe_baked\\";
//      folder = "C:\\Users\\Igor\\Documents\\My Dropbox\\MCExamples\\Examples\\BookExamples\\MCGraphs\\";

//      folder="C:\\Users\\Igor\\Documents\\My Dropbox\\MCExamples\\31-3-11\\CarstenAprove09GCD_RankingStructure\\";

        folder="C:\\Users\\Igor\\Documents\\My Dropbox\\fred_20-4-11\\pe_fred.8.2.2011\\";

        ExamplesRunner.testFolder(folder,false);



//        LightProgram.main(new String[] {});
    }
}
