package com.expungement.alloy.alloyrunner.controller;

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
import com.expungement.alloy.alloyrunner.service.AlloyService;

@RestController
@RequestMapping("/api/alloy")
@CrossOrigin(origins = "http://localhost:3000")
public class AlloyController {

	@GetMapping("/")
	public String hello() {
		return "Hello World";
	}
	
	@Autowired
    private AlloyService alloyService;

	@PostMapping("/run")
    public ResponseEntity<?> runModel(@RequestBody AlloyRequest request) {
        try {
            JSONObject result = alloyService.runAlloyModel(request.getPredicate(), request.getRun());
            return ResponseEntity.ok(result.toString(4));
        } catch (Exception e) {
            return ResponseEntity.internalServerError().body("Failed to run model: " + e.getMessage());
        }
    }
}
