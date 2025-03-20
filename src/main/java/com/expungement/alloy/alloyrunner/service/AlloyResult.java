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
import jakarta.annotation.PostConstruct;
import kodkod.engine.satlab.SATFactory;

import java.util.regex.*;
import java.util.*;
import java.util.concurrent.CompletableFuture;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

@Service
public class AlloyResult {

    @Value("${alloy.model.path}")
    private String modelPath = "";

    @Value("${alloy.model.path2}")
    private String modelPath2 = "";

    /**
     * Asynchronous method to evaluate an Alloy query.
     */
    public CompletableFuture<JSONObject> evaluateAlloyQueryAsync(String predicate, String run, String type) {
        return CompletableFuture.supplyAsync(() -> evaluateAlloyQuery(predicate, run, type));
    }

    public JSONObject evaluateAlloyQuery(String predicate, String run, String type) {
        String modelContent;
        
        String userPredicate = "\n\npred userDefinedPredicate {\n"
        	    + predicate
        	    + "}\n"
        	    + run;
        

        try {
            // Read the existing model from file
        	if(type.equals("forward")) {
                modelContent = new String(Files.readAllBytes(Paths.get(modelPath)));
        	}else {
                modelContent = new String(Files.readAllBytes(Paths.get(modelPath2)));
        	}
            // Append the user-defined predicate at the end of the model
            modelContent += userPredicate;

            // Parse the modified Alloy model from string
            Module world = CompUtil.parseEverything_fromString(null, modelContent);

            // Options for the Alloy solver
            A4Options options = new A4Options();
            options.solver = SATFactory.get("minisat");


            // Execute the model
            A4Solution solution = TranslateAlloyToKodkod.execute_command(null, world.getAllReachableSigs(), world.getAllCommands().get(world.getAllCommands().size() - 1), options);

            // Process the solution
            if (solution.satisfiable()) {
                JSONArray eventData = convertToJSONArray(solution.toString());
                System.out.println(eventData);
                return formatOutput(!eventData.isEmpty(), eventData);
            } else {
                return formatOutput(false, new JSONArray());
            }
        } catch (Err | IOException e) {
            e.printStackTrace();
            return formatOutput(false, new JSONArray());
        }
    }

    private JSONObject formatOutput(boolean success, JSONArray data) {
        JSONObject result = new JSONObject();
        result.put("success", success);
        result.put("data", data);
        System.out.println(result);
        return result;
    }

    public JSONArray convertToJSONArray(String alloyOutput) {
        JSONArray eventList = new JSONArray();
        Map<String, String> eventToIdMap = parseUserDefinedPredicates(alloyOutput);
        
        int lastStateIndex = alloyOutput.lastIndexOf("------State ");
        if (lastStateIndex == -1) {
            System.out.println("No states found in Alloy output.");
            return eventList;
        }

        // Extract the last state directly
        String lastState = alloyOutput.substring(lastStateIndex).trim();

        System.out.println("Processing last state:\n" + lastState);

        // Build a map of events to dates for quick lookup
        Map<String, String> eventDateMap = new HashMap<>();
        Matcher eventDateMatcher = Pattern.compile("this/Event<:date=\\{([^}]*)\\}").matcher(lastState);
        if (eventDateMatcher.find()) {
            String[] eventDatePairs = eventDateMatcher.group(1).split(",\\s*");
            for (String pair : eventDatePairs) {
                String[] parts = pair.split("->");
                if (parts.length == 2) {
                    eventDateMap.put(parts[0].trim(), parts[1].trim());
                }
            }
        } else {
            System.out.println("No event-date pairs found.");
        }

        // Iterate over known events and check if they have associated dates
        for (String event : eventDateMap.keySet()) {
            String date = eventDateMap.get(event);

            if (event.startsWith("Expungement")) {
                continue;
            }

            // Create JSON object for each event
            JSONObject entry = new JSONObject();
            entry.put("id", eventToIdMap.getOrDefault(event, ""));
            entry.put("event", event);
            entry.put("date", date);
            entry.put("owi", isEventInSet(lastState, "this/OWI", event));
            entry.put("tenner", isEventInSet(lastState, "this/TenYearFelony", event));
            entry.put("assaultive", isEventInSet(lastState, "this/Assaultive", event));
            entry.put("expunged", isEventInSet(lastState, "this/pastExpunged", event));

            // Add violations
            entry.put("violations", getViolationsForEvent(lastState, event));

            eventList.put(entry);
        }

        return eventList;
    }

    private Map<String, String> parseUserDefinedPredicates(String alloyOutput) {
        Map<String, String> eventToIdMap = new HashMap<>();
        Matcher predicateMatcher = Pattern.compile("skolem \\$(userDefinedPredicate_\\w+)=\\{([^}]*)\\}").matcher(alloyOutput);
        while (predicateMatcher.find()) {
            String id = predicateMatcher.group(1).replace("userDefinedPredicate_", "");
            String[] events = predicateMatcher.group(2).split(",\\s*");
            for (String event : events) {
                eventToIdMap.put(event, id);
            }
        }
        return eventToIdMap;
    }

    private boolean isEventInSet(String state, String setName, String event) {
        Pattern pattern = Pattern.compile(setName + "=\\{([^}]*)\\}");
        Matcher matcher = pattern.matcher(state);
        if (matcher.find()) {
            String[] setItems = matcher.group(1).split(",\\s*");
            return Arrays.asList(setItems).contains(event);
        }
        return false;
    }

    private JSONArray getViolationsForEvent(String state, String event) {
        JSONArray violations = new JSONArray();
        String[] violationTypes = {
                "sec1_1bViolations", "sec1_1cViolations", "sec1d_2Violations",
                "sec1dTimingViolations", "backwardWaitingViolations", "forwardWaitingViolations"
        };

        for (String violationType : violationTypes) {
            if (isEventInSet(state, "this/" + violationType, event)) {
                violations.put(violationType);
            }
        }

        return violations;
    }
}
