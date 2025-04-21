# Formal Security Analysis for the Secure Swarm Toolkit (SST)

Authors: Hokeun Kim, Eunsuk Kang, Edward Lee, David Bronman    
Contact: hokeunkim@eecs.berkeley.edu or eunsuk.kang@berkeley.edu

## Introduction 

This repository contains a model of the authentication and authorization protocol in the Secure Swarm Toolkit (SST) in Alloy. Alloy is a formal modeling language based on a first-order relational logic with transitive closure. The underlying analysis engine, the Alloy Aanlyzer, can be used to perform simulation and automatic verification of a model against various types of properties, including security. The Alloy Analyzer is available for download at alloy.mit.edu.

We've performed a verification of the SST protocol model to check whether it satisfies the confidentiality and authenticity of the communication among trusted entities on an SST network.

## Content of the repository:

model/   
  Auth.als: An Alloy model of the SST protocol   
  Auth.thm: A custom visualization theme for the Alloy model   



## Clone repository

```bash
git clone https://github.com/iotauth/security_analysis.git
```


# Download Alloy

## Mac with Apple Silicon
1. Download [alloy-6.2.0-mac-aarch64.zip](https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.2.0/alloy-6.2.0-mac-aarch64.zip)
2. Unzip and move `Alloy` file to the `/Applications` folder

### ⚠️ MacOS Security Prompt

If you see a warning message, *"Error “Alloy” Not opened: Apple could not verify “Alloy” is free of malware that may harm your Mac or compromise your privacy,"* follow these steps:

1. Close the warning by clicking `Done`
2. Open `System Settings > Privacy & Security`
3. Scroll down to the message about Alloy being blocked
4. Click `Open Anyway` and confirm with your password



## Run the Alloy Model

Once Alloy is installed and the repository is cloned, folow these steps to run the alaysis:

1. Launch Alloy
2. Open the file `/security_analysis/model/Analysis.als`
3. Click **Execute**
4. To view the results in the visualizer, click **Show**


  
  
  
  
