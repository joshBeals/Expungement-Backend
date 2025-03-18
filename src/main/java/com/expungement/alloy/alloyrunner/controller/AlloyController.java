package com.expungement.alloy.alloyrunner.controller;

import java.util.concurrent.CompletableFuture;

import org.json.JSONObject;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;

import com.expungement.alloy.alloyrunner.model.AlloyRequest;
import com.expungement.alloy.alloyrunner.service.AlloyResult;
import com.expungement.alloy.alloyrunner.service.AlloyService;

@RestController
@RequestMapping("/api/alloy")
public class AlloyController {

	@GetMapping("/")
	public String hello() {
		return "Hello World";
	}
	
	@Autowired
    private AlloyService alloyService;
	@Autowired
    private AlloyResult alloyResult;

	@PostMapping("/run")
    public ResponseEntity<?> runModel(@RequestBody AlloyRequest request) {
        try {
            JSONObject result = alloyService.runAlloyModel(request.getPredicate(), request.getRun(), request.getType());
            return ResponseEntity.ok(result.toString(4));
        } catch (Exception e) {
            return ResponseEntity.internalServerError().body("Failed to run model: " + e.getMessage());
        }
    }
	
	@PostMapping("/evaluate")
    public CompletableFuture<ResponseEntity<String>> evaluateQuery(@RequestBody AlloyRequest request) {
        return alloyResult.evaluateAlloyQueryAsync(request.getPredicate(), request.getRun(), request.getType())
                .thenApply(result -> ResponseEntity.ok(result.toString(4)))
                .exceptionally(ex -> ResponseEntity.internalServerError().body("Failed to validate model: " + ex.getMessage()));
    }

}
