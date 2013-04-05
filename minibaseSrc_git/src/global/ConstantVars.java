package global;

public final class ConstantVars {
	private static RID globalRID;
	
	public static final void setGlobalRID(RID rid){
		if(globalRID==null)
			globalRID = new RID();
		globalRID.slotNo = rid.slotNo;
		globalRID.pageNo = rid.pageNo;
	}
	
	public static final RID getGlobalRID(){
		return globalRID;
	}
}
