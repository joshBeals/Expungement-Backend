package com.expungement.alloy.alloyrunner.model;

public class AlloyRequest {
	
	private String predicate;
    private String run;
    private String type;

    // Getters and setters
    public String getPredicate() {
        return predicate;
    }

    public void setPredicate(String predicate) {
        this.predicate = predicate;
    }

    public void setType(String type) {
        this.type = type;
    }
    
    public String getRun() {
        return run;
    }

    public String getType() {
        return type;
    }

    public void setRun(String run) {
        this.run = run;
    }
}
