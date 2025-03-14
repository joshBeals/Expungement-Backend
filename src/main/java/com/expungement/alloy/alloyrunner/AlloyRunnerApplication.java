package com.expungement.alloy.alloyrunner;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.CommandLineRunner;
import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.context.annotation.PropertySource;
import org.springframework.core.env.Environment;

@SpringBootApplication
@PropertySource("classpath:application.properties")
public class AlloyRunnerApplication implements CommandLineRunner {

    @Autowired						
    private Environment env;

    public static void main(String[] args) {
    	try {
            SpringApplication.run(AlloyRunnerApplication.class, args);
        } catch (Exception e) {
            e.printStackTrace();  // Print exception details if the app crashes
        }
    }

    @Override
    public void run(String... args) {
        System.out.println("alloy.model.path: " + env.getProperty("alloy.model.path"));
        System.out.println("alloy.model.path2: " + env.getProperty("alloy.model.path2"));
    }
}
