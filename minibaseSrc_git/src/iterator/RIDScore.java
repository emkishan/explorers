package iterator;

import global.RID;

public class RIDScore {
	private RID rid;
	private float score;
	
	public RIDScore(RID rid, float score) {
		this.rid=rid;
		this.score=score;
	}
	
	public RID getRid() {
		return rid;
	}
	public void setRid(RID rid) {
		this.rid = rid;
	}
	public float getScore() {
		return score;
	}
	public void setScore(float score) {
		this.score = score;
	}
	
	
}
