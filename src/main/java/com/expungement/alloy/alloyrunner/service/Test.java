package com.expungement.alloy.alloyrunner.service;

import org.json.JSONObject;

import org.json.JSONArray;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.stereotype.Service;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

import java.util.regex.*;
import java.util.*;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

@Service
public class Test {
	
	@Value("${alloy.model.path}")
    private String modelPath = "";

    public JSONObject runAlloyModel(String predicate, String run) {
        String modelContent;
        
        String userPredicate = "\n\npred userDefinedPredicate {\n"
        	    + predicate
        	    + "}\n"
        	    + run;
        System.out.println(userPredicate);

        try {
            // Read the existing model from file
            modelContent = new String(Files.readAllBytes(Paths.get(modelPath)));
            // Append the user-defined predicate at the end of the model
            modelContent += userPredicate;

            // Parse the modified Alloy model from string
            Module world = CompUtil.parseEverything_fromString(null, modelContent);

            // Options for the Alloy solver
            A4Options options = new A4Options();
            options.solver = A4Options.SatSolver.SAT4J;

            // Execute the model
            A4Solution solution = TranslateAlloyToKodkod.execute_command(null, world.getAllReachableSigs(), world.getAllCommands().get(world.getAllCommands().size() - 1), options);

            // Process the solution
            if (solution.satisfiable()) {
                // Convert solution to JSON
            	System.out.println(solution.toString());
                JSONObject jsonOutput = convertToJSON(solution.toString());
                return jsonOutput;
            } else {
                System.out.println("No solution found.");
                return new JSONObject().put("error", "No solution found.");
            }
        } catch (Err e) {
            e.printStackTrace();
            return new JSONObject().put("error", "Error during Alloy model execution: " + e.getMessage()).put("success", false);
        } catch (IOException e) {
            e.printStackTrace();
            return new JSONObject().put("error", "Error reading the Alloy model file: " + e.getMessage()).put("success", false);
        }
    }

    private JSONObject convertToJSON(String alloyOutput) {
    	// Use regex to split input by "------State X-------"
        String[] states = alloyOutput.split("------State \\d+-------\n");
        JSONArray jsonStates = new JSONArray();
        int stateIndex = 0;

        for (String state : states) {
            if (state.trim().isEmpty()) continue;

            JSONObject jsonState = new JSONObject();
            jsonState.put("state", stateIndex++);
            
            Matcher matcher = Pattern.compile("this/now=\\{([^}]*)\\}").matcher(state);
            if (matcher.find()) {
                jsonState.put("now", new JSONArray(matcher.group(1).split(",\\s*")));
            } else {
                jsonState.put("now", new JSONArray());
            }

            matcher = Pattern.compile("this/Event=\\{([^}]*)\\}").matcher(state);
            if (matcher.find()) {
                jsonState.put("events", new JSONArray(matcher.group(1).split(",\\s*")));
            }

            matcher = Pattern.compile("this/Event<:date=\\{([^}]*)\\}").matcher(state);
            if (matcher.find()) {
                String[] relations = matcher.group(1).split(",\\s*");
                JSONObject eventDateRelationships = new JSONObject();
                for (String relation : relations) {
                    String[] parts = relation.split("->");
                    eventDateRelationships.put(parts[0], parts[1]);
                }
                jsonState.put("event_date", eventDateRelationships);
            }
            
            matcher = Pattern.compile("this/pastExpunged=\\{([^}]*)\\}").matcher(state);
            if (matcher.find()) {
                jsonState.put("expunged", new JSONArray(matcher.group(1).split(",\\s*")));
            } else {
                jsonState.put("expunged", new JSONArray());
            }

            // Initialize the date attributes object
            JSONObject dateAttributes = new JSONObject();
            dateAttributes.put("withinFive", new JSONArray());
            dateAttributes.put("withinSix", new JSONArray());
            dateAttributes.put("withinSeven", new JSONArray());
            jsonState.put("date_attributes", dateAttributes);

            jsonStates.put(jsonState);
        }

        JSONObject result = new JSONObject();
        result.put("success", true);
        result.put("data", jsonStates);
        return result;
    }
}
