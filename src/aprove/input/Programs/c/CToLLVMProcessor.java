package aprove.input.Programs.c;

import java.io.*;
import java.util.*;

import aprove.Globals;
import aprove.input.Programs.llvm.Translator;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Transforms (= compiles) a C program to an LLVM program by using Clang.
 * @author ffrohn
 * @version $Id$
 */
public class CToLLVMProcessor extends Processor.ProcessorSkeleton {

    /**
     * @return A path to a temporary file (used for the compiled LLVM program).
     */
    private static String getTmpFileName() {
        String tmpDir = System.getProperty("java.io.tmpdir");
        String separator = System.getProperty("file.separator");
        UUID tmpFileName = UUID.randomUUID();
        return tmpDir + separator + tmpFileName;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.Processor#isApplicable(aprove.prooftree.Obligations.BasicObligation)
     */
    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof CProblem;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.Processor#process(aprove.prooftree.Obligations.BasicObligation, aprove.prooftree.Obligations.BasicObligationNode, aprove.strategies.Abortions.Abortion, aprove.strategies.ExecutableStrategies.RuntimeInformation)
     */
    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
    throws AbortionException {
        CProblem cObl = (CProblem)obl;
        String path = cObl.getPath();
        Globals.programFile = path;
        Translator llvmTranslator = new Translator(cObl.getQuery());
        String llvmFileName = CToLLVMProcessor.getTmpFileName();
        try {
            // Always compile with debug information (-g): besides being needed for witness generation, the debug
            // metadata lets us recover the source-level signedness of variables (see LLVMModule#getDebugUnsignedAllocas),
            // which is otherwise lost when clang lowers e.g. "unsigned int" to "i32".
            Process clang = Runtime.getRuntime().exec("clang " + path + " -S -emit-llvm -g -o " + llvmFileName);
            clang.waitFor();
            @SuppressWarnings("resource")
            InputStream stderr = clang.getErrorStream();
            byte[] buffer = new byte[1024];
            while (stderr.available() > 0) {
                int read = stderr.read(buffer);
                System.err.println(new String(Arrays.copyOfRange(buffer, 0, read)));
            }
            llvmTranslator.translate(new File(llvmFileName));
        } catch (IOException | TranslationException | InterruptedException e) {
            e.printStackTrace(System.err);
            return ResultFactory.unsuccessful(e.getMessage());
        }
        return
            ResultFactory.proved(
                llvmTranslator.getState().setFileToRemove(new File(llvmFileName)).setFromC(),
                YNMImplication.EQUIVALENT,
                new CToLLVMProof(path)
            );
    }

    /**
     * A proof that we compiled a C file to LLVM.
     * @author ffrohn
     * @version $Id$
     */
    public static class CToLLVMProof extends DefaultProof {

        /**
         * The path to the C file.
         */
        private String path;

        /**
         * @param path The path to the C file.
         */
        public CToLLVMProof(String path) {
            this.path = path;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Utility.VerbosityExportable#export(aprove.prooftree.Export.Utility.Export_Util, aprove.verification.oldframework.Utility.VerbosityLevel)
         */
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Compiled c-file " + this.path + " to LLVM.";
        }

    }
}
