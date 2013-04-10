package global;

public final class ConstantVars {
	private static RID globalRID;
	private static int readCount;
	private static int writeCount;
	private static int allocateCount;
	
	public static final void setGlobalRID(RID rid){
		if(globalRID==null)
			globalRID = new RID();
		globalRID.slotNo = rid.slotNo;
		globalRID.pageNo = rid.pageNo;
	}
	
	public static final RID getGlobalRID(){
		return globalRID;
	}
	
	public static final void incrementReadCount(){
		readCount++;
	}
	
	public static final int getReadCount(){
		return readCount;
	}
	
	public static final void incrementWriteCount(){
		writeCount++;
	}
	
	public static final int getWriteCount(){
		return writeCount;
	}
}
