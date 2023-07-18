Mean_X<-0
Stdev_X<-0.75
Theta<-c(-1,0.8)
N<-5000
All_Models<-list(Real_Model=c("X0","X1"),
                 Assumed_Model_1=c("X0","X1","X1^2"))

Generate_Data<-function(Mean_X,Stdev_X,Theta,N,All_Models)
{
  X<-mvnfast::rmvn(n = N, mu= Mean_X,sigma=Stdev_X)
  Complete_Data<-cbind(1,X,X^2)
  colnames(Complete_Data)<-c(paste0("X",0:length(Mean_X)),
                             paste0("X",1:length(Mean_X),"^2"))
  
  Pi_Data <-LaplacesDemon::invlogit(Complete_Data[,colnames(Complete_Data) %in% All_Models$Real_Model]%*%Theta)
  Y_Data <- LaplacesDemon::rbern(N,Pi_Data)
  
  All_Data<-list()
  for (i in 1:length(All_Models)) 
  {
    All_Data[[i]]<-cbind(Y=Y_Data,Complete_Data[,colnames(Complete_Data) %in% All_Models[[i]] ])
  }
  
  names(All_Data)<-names(All_Models)
  
  Simulated_Data<-list("Basic"=list("N"=N,
                                    "Theta"=Theta,
                                    "Mean_X"=Mean_X,
                                    "Stdev_X"=Stdev_X,
                                    "Pi"=Pi_Data),
                       "All_Data"=All_Data)
  
  return(Simulated_Data)
}

Simulated_Data<-Generate_Data(Mean_X,Stdev_X,Theta,N,All_Models)

remove(Mean_X,Stdev_X,N,Theta)

r1<-100
r0<-50

# Optimal Sampling and MROS ----
# Newton Rhapson Algorithm for MLE 
getMLE <- function(x, y, w) {
  beta <- rep(0, ncol(x))
  loop  <- 1
  Loop  <- 200
  msg <- "NA"
  while (loop <= Loop) {
    pr <- c(1 - 1 / (1 + exp(x %*% beta)))
    H <- t(x) %*% (pr * (1 - pr) * w * x)
    S <- colSums((y - pr) * w * x)
    tryCatch(
      {shs <- NA
      shs <- solve(H, S) }, 
      error=function(e){
        cat("\n ERROR :", loop, conditionMessage(e), "\n")})
    if (is.na(shs[1])) {
      msg <- "Not converge"
      beta <- loop <- NA
      break
    }
    beta.new <- beta + shs
    tlr  <- sum((beta.new - beta)^2)
    beta  <- beta.new
    if(tlr < 0.000001) {
      msg <- "Successful convergence"
      break
    }
    if (loop == Loop)
      warning("Maximum iteration reached")
    loop  <- loop + 1
  }
  list(par=beta, message=msg, iter=loop)
}

# Two step OSMAC ----
AlgTwoStp <- function(r0,r1,Y,X,n,Real_Data,alpha,combs,All_Covariates){
  Y_Real<-Real_Data[,1] #  Real Data
  X_Real<-Real_Data[,-1] # Real Data
  
  n1 <- sum(Y)
  n0 <- n - n1
  PI.prop <- rep(1/(2*n0), n)
  PI.prop[Y==1] <- 1/(2*n1)
  idx.prop <- sample(1:n, r0, T, PI.prop)
  
  x.prop<-lapply(1:length(combs),function(a){
    X[idx.prop,All_Covariates %in% combs[[a]]] # Assumed Data 
  })
  y.prop <- Y[idx.prop]  # Assumed Data 
  
  x_Real.prop<-X_Real[idx.prop,] # Real Data
  y_Real.prop<-Y_Real[idx.prop] # Real Data
  
  pinv.prop <- n
  pinv.prop <- 1/PI.prop[idx.prop]
  
  fit.prop <- lapply(1:length(combs), function(a){
    getMLE(x=x.prop[[a]], y=y.prop, w=pinv.prop) # Assumed Data
  })
  fit_Real.prop <- getMLE(x=x_Real.prop, y=y_Real.prop, w=pinv.prop) # Real Data
  
  beta.prop<-list()
  for (j in 1:length(combs)) 
  {
    beta.prop[[j]] <- fit.prop[[j]]$par # Assumed Data
    if(anyNA(beta.prop[[j]]))
    {
      return(list(opt=NA, msg="first stage not converge"))
    }
  }
  beta_Real.prop <- fit_Real.prop$par # Real Data
  
  if(anyNA(beta_Real.prop[1]))
    return(list(opt=NA, msg="first stage not converge"))
  
  P.prop  <- lapply(1:length(combs),function(a){
    1 - 1 / (1 + exp(X[,All_Covariates %in% combs[[a]] ] %*% beta.prop[[a]])) # Assumed Data
  })
  P_Real.prop  <- 1 - 1 / (1 + exp(X_Real %*% beta_Real.prop)) # Real Data
  
  # For the Real Model 
  beta.mMSE_Real <- NULL
  Index.mMSE_Real <- NULL
  
  # For the Assumed Model with Already Available Sub-sampling probabilities
  beta.mMSE_Old<-list()
  Index.mMSE_Assumed_Old<-matrix(nrow = r1,ncol = length(combs))
  
  # For the Real Model with joined Sub-sampling probabilities
  beta.mMSE_join<-NULL
  Index.mMSE_join<-NULL
  
  ## mMSE
  p_Real.prop <- P_Real.prop[idx.prop] # Real data
  w_Real.prop <- p_Real.prop * (1 - p_Real.prop) # Real data
  W_Real.prop <- solve(t(x_Real.prop) %*% (x_Real.prop * w_Real.prop * pinv.prop)) # Real data
  
  p_Assumed.prop <- lapply(1:length(combs),function(a){
    P.prop[[a]][idx.prop] # Assumed data
  })
  w_Assumed.prop <- lapply(1:length(combs),function(a){
    p_Assumed.prop[[a]] * (1 - p_Assumed.prop[[a]]) # Assumed data
  })
  W_Assumed.prop <- lapply(1:length(combs),function(a){
    solve(t(x.prop[[a]]) %*% (x.prop[[a]] * w_Assumed.prop[[a]] * pinv.prop)) # Assumed data
  })
  
  PI_Real.mMSE <- sqrt((Y_Real - P_Real.prop)^2 * rowSums((X_Real%*%W_Real.prop)^2)) # Real data
  PI_Real.mMSE <- PI_Real.mMSE / sum(PI_Real.mMSE) # Real data
  
  PI_Assumed_Old.mMSE <- lapply(1:length(combs),function(a){
    sqrt((Y - P.prop[[a]])^2 * rowSums((X[,All_Covariates %in% combs[[a]] ]%*%W_Assumed.prop[[a]])^2)) # Assumed data
  })
  
  PI_Assumed_Old.mMSE <- lapply(1:length(combs),function(a){
    PI_Assumed_Old.mMSE[[a]] / sum(PI_Assumed_Old.mMSE[[a]]) # Assumed data
  })
  
  PI_join.mMSE<-matrixStats::rowSums2(cbind(alpha[1]*PI_Real.mMSE,
                                            (do.call(cbind,PI_Assumed_Old.mMSE)%*%diag(alpha[-1]))))
  
  ## mMSE
  idx_Real.mMSE <- sample(1:n, r1-r0, T, PI_Real.mMSE) # Real data
  idx_Assumed.mMSE <- lapply(1:length(combs),function(a){
      sample(1:n, r1-r0, T, PI_Assumed_Old.mMSE[[a]]) # Assumed data
    }) 
  idx_join.mMSE <- sample(1:n, r1-r0, T, PI_join.mMSE) # Joined Data
    
  x_Real.mMSE <- X_Real[c(idx_Real.mMSE, idx.prop),] # Real Data
  y_Real.mMSE <- Y_Real[c(idx_Real.mMSE, idx.prop)] # Real Data
    
  x_Assumed.mMSE <- lapply(1:length(combs),function(a){
      X_Real[c(idx_Assumed.mMSE[[a]], idx.prop),] # Assumed Data
    })
  y_Assumed.mMSE <- lapply(1:length(combs),function(a){
      Y_Real[c(idx_Assumed.mMSE[[a]], idx.prop)] # Assumed Data
    })
    
  x_join.mMSE <- X_Real[c(idx_join.mMSE, idx.prop),] # Joined Data
  y_join.mMSE <- Y_Real[c(idx_join.mMSE, idx.prop)] # Joined Data
    
  fit_Real.mMSE <- getMLE(x=x_Real.mMSE, y=y_Real.mMSE, 
                            w=c(1 / PI_Real.mMSE[idx_Real.mMSE], pinv.prop)) # Real Data
  fit_Assumed_Old.mMSE <- lapply(1:length(combs),function(a){
      getMLE(x=x_Assumed.mMSE[[a]], y=y_Assumed.mMSE[[a]], 
             w=c(1 / PI_Assumed_Old.mMSE[[a]][idx_Assumed.mMSE[[a]]], pinv.prop)) # Assumed Data Old probabilities
    })
    
  fit_join.mMSE <- getMLE(x=x_join.mMSE, y=y_join.mMSE, 
                            w=c(1 / PI_join.mMSE[idx_join.mMSE], pinv.prop)) # Joined Data 
    
  Index.mMSE_Real<-c(idx_Real.mMSE,idx.prop) # Real Data
    
  for (j in 1:length(combs))
  {
    Index.mMSE_Assumed_Old[,j]<-c(idx_Assumed.mMSE[[j]], idx.prop) # Assumed Data Old probabilities
  }

  Index.mMSE_join<-c(idx_join.mMSE, idx.prop) # Joined Data
    
  if(anyNA(fit_Real.mMSE$par) || anyNA(fit_Assumed_Old.mMSE$par) || anyNA(fit_join.mMSE$par))
  {
    stop("There are NA or NaN values")
  }
    
  beta.mMSE_Real <- fit_Real.mMSE$par # Real Data
  for (j in 1:length(combs)) 
  {
    beta.mMSE_Old[[j]] <- fit_Assumed_Old.mMSE[[j]]$par # Assumed Data Old probabilities 
  }
  beta.mMSE_join <- fit_join.mMSE$par # Joined Data
  
  Full_SP_Real<-PI_Real.mMSE
  Full_SP_Old<-do.call(cbind,PI_Assumed_Old.mMSE)
  Full_SP_join<-PI_join.mMSE
   
  opt_Real<-list("Est_Theta_mMSE"=beta.mMSE_Real)
  
  for(j in 1:length(combs))
  {
    assign(paste0("opt_Old_",j),list("Est_Theta_mMSE"=beta.mMSE_Old[[j]]))
  }
  
  opt_join<-list("Est_Theta_mMSE"=beta.mMSE_join)
  
  msg <- c(fit.prop$message, fit_Real.prop$message,
           fit_Real.mMSE$message,fit_Assumed_Old.mMSE$message,fit_join.mMSE$message)
  #msg <- NULL
  return(list(opt=list("opt_Real"=opt_Real,
                       "opt_Old"=mget(paste0("opt_Old_",1:length(combs))),
                       "opt_join"=opt_join,
                       "SP"=cbind(Full_SP_Real,Full_SP_Old,Full_SP_join),
                       "Index"=cbind(Index.mMSE_Real,Index.mMSE_Assumed_Old,Index.mMSE_join)), msg=msg)) 
}

Optimal_Sampling<-AlgTwoStp(r0,r1,
                            Y=Simulated_Data$All_Data$Real_Model[,1],
                            X=Simulated_Data$All_Data$Real_Model[,-1],
                            n=Simulated_Data$Basic$N,
                            Real_Data=Simulated_Data$All_Data$Real_Model,
                            alpha=rep(1/length(All_Models),length(All_Models)),
                            combs=All_Models[2:4],
                            All_Covariates=All_Models[[1]])

# Random Sampling ----
Run_RandomSample <- function(FullData,Subsample_Size,index)
{
  Full_Sample<-1:nrow(FullData)
  Sampled<-sample(Full_Sample[-index],size = Subsample_Size)
  Random_Sample<-as.data.frame(FullData[c(Sampled,index),])
  
  Results<-glm(Y~.-1,data=Random_Sample,family = binomial)
  Est_Parameter<-Results$coefficients
  
  return(list("RS_Index"=c(Sampled,index),"Parameter"=Est_Parameter))
}

Random_Sample<-Run_RandomSample(FullData = Simulated_Data$All_Data$Real_Model,
                                Subsample_Size = r0,
                                index=Optimal_Sampling$opt$Index[(r1-r0+1):r1,1])

# Sampled Data Plots

Sample_Data<-rbind(cbind.data.frame("Method"="Full Data",Simulated_Data$All_Data$Real_Model,"SP"=1),
                   cbind.data.frame("Method"="Random Sampling",Simulated_Data$All_Data$Real_Model[Random_Sample$RS_Index[1:(r1-r0)],],
                                    "SP"=1/Simulated_Data$Basic$N),
                   cbind.data.frame("Method"="Optimal Sampling DM",Simulated_Data$All_Data$Real_Model[Optimal_Sampling$opt$Index[1:(r1-r0),1],],
                                    "SP"=Optimal_Sampling$opt$SP[Optimal_Sampling$opt$Index[1:(r1-r0),1],1]),
                   cbind.data.frame("Method"="Optimal Sampling AM 1",Simulated_Data$All_Data$Real_Model[Optimal_Sampling$opt$Index[1:(r1-r0),2],],
                                    "SP"=Optimal_Sampling$opt$SP[Optimal_Sampling$opt$Index[1:(r1-r0),2],2]),
                   cbind.data.frame("Method"="Optimal Sampling AM 2",Simulated_Data$All_Data$Real_Model[Optimal_Sampling$opt$Index[1:(r1-r0),3],],
                                    "SP"=Optimal_Sampling$opt$SP[Optimal_Sampling$opt$Index[1:(r1-r0),3],3]),
                   cbind.data.frame("Method"="Optimal Sampling AM 3",Simulated_Data$All_Data$Real_Model[Optimal_Sampling$opt$Index[1:(r1-r0),4],],
                                    "SP"=Optimal_Sampling$opt$SP[Optimal_Sampling$opt$Index[1:(r1-r0),4],4]),
                   cbind.data.frame("Method"="Model Robust Optimal Sampling DM",Simulated_Data$All_Data$Real_Model[Optimal_Sampling$opt$Index[1:(r1-r0),5],],
                                    "SP"=Optimal_Sampling$opt$SP[Optimal_Sampling$opt$Index[1:(r1-r0),5],5])) 

Sampling_Methods<-c("Full Data","Random Sampling","Optimal Sampling DM",
                    "Optimal Sampling DM","Optimal Sampling AM 1","Optimal Sampling AM 2","Optimal Sampling AM 3",
                    "Model Robust Optimal Sampling DM")

ggplot(Sample_Data[Sample_Data$Method %in% Sampling_Methods[c(1,2)],],aes(x=X1,y=X2,color=SP))+
  geom_point()+theme_light()+scale_color_viridis_c()+
  gghighlight(Method!="Full Data")+ggtitle("Random Sampling : Data Model")->p1

ggplot(Sample_Data[Sample_Data$Method %in% Sampling_Methods[c(1,3)],],aes(x=X1,y=X2,color=SP))+
  geom_point()+theme_light()+scale_color_viridis_c()+
  gghighlight(Method!="Full Data")+ggtitle("Optimal Sampling : Data Model")->p2

ggplot(Sample_Data[Sample_Data$Method %in% Sampling_Methods[c(1,4)],],aes(x=X1,y=X2,color=SP))+
  geom_point()+theme_light()+scale_color_viridis_c()+
  gghighlight(Method!="Full Data")+ggtitle("Optimal Sampling : Assumed Model 1")->p3

ggplot(Sample_Data[Sample_Data$Method %in% Sampling_Methods[c(1,5)],],aes(x=X1,y=X2,color=SP))+
  geom_point()+theme_light()+scale_color_viridis_c()+
  gghighlight(Method!="Full Data")+ggtitle("Optimal Sampling : Assumed Model 2")->p4

ggplot(Sample_Data[Sample_Data$Method %in% Sampling_Methods[c(1,6)],],aes(x=X1,y=X2,color=SP))+
  geom_point()+theme_light()+scale_color_viridis_c()+
  gghighlight(Method!="Full Data")+ggtitle("Optimal Sampling : Complex Model")->p5

ggplot(Sample_Data[Sample_Data$Method %in% Sampling_Methods[c(1,7)],],aes(x=X1,y=X2,color=SP))+
  geom_point()+theme_light()+scale_color_viridis_c()+
  gghighlight(Method!="Full Data")+ggtitle("Model Robust Optimal Sampling : Data Model")->p6

ggarrange(p1,p2,p3,p4,p5,p6,nrow = 2,ncol=3,legend = "right")
ggsave("Subsample_Data.jpg",width = 3*8,height = 2*6)

SP_Data<-rbind(cbind.data.frame("Method"="Random Sampling","SP"=rep(1/Simulated_Data$Basic$N,Simulated_Data$Basic$N),
                                Simulated_Data$All_Data$Real_Model),
               cbind.data.frame("Method"="Optimal Sampling DM","SP"=Optimal_Sampling$opt$SP[,1],
                                Simulated_Data$All_Data$Real_Model),
               cbind.data.frame("Method"="Optimal Sampling AM 1","SP"=Optimal_Sampling$opt$SP[,2],
                                Simulated_Data$All_Data$Real_Model),
               cbind.data.frame("Method"="Optimal Sampling AM 2","SP"=Optimal_Sampling$opt$SP[,3],
                                Simulated_Data$All_Data$Real_Model),
               cbind.data.frame("Method"="Optimal Sampling AM 3","SP"=Optimal_Sampling$opt$SP[,4],
                                Simulated_Data$All_Data$Real_Model),
               cbind.data.frame("Method"="Model Robust Optimal Sampling DM","SP"=Optimal_Sampling$opt$SP[,5],
                                Simulated_Data$All_Data$Real_Model))

ggplot(SP_Data,aes(x=X1,y=SP,group=Method))+
  geom_point(color="blue")+facet_wrap(~Method)+theme_light()

# Full Data ----
Sample_Data<-rbind(cbind.data.frame("Method"="Full Data",Simulated_Data$All_Data$Real_Model,"SP"=1),
                   cbind.data.frame("Method"="Random Sampling",Simulated_Data$All_Data$Real_Model,"SP"=1/Simulated_Data$Basic$N),
                   cbind.data.frame("Method"="Optimal Sampling DM",Simulated_Data$All_Data$Real_Model,"SP"=Optimal_Sampling$opt$SP[,1]),
                   cbind.data.frame("Method"="Optimal Sampling AM 1",Simulated_Data$All_Data$Real_Model,"SP"=Optimal_Sampling$opt$SP[,2]),
                   cbind.data.frame("Method"="Optimal Sampling AM 2",Simulated_Data$All_Data$Real_Model,"SP"=Optimal_Sampling$opt$SP[,3]),
                   cbind.data.frame("Method"="Optimal Sampling AM 3",Simulated_Data$All_Data$Real_Model,"SP"=Optimal_Sampling$opt$SP[,4]),
                   cbind.data.frame("Method"="Model Robust Optimal Sampling DM",Simulated_Data$All_Data$Real_Model,"SP"=Optimal_Sampling$opt$SP[,5])) 

ggplot(Sample_Data[Sample_Data$Method %in% Sampling_Methods[c(1,2)],],aes(x=X1,y=X2,color=SP))+
  geom_point()+theme_light()+scale_color_viridis_c()+
  gghighlight(Method!="Full Data")+ggtitle("Random Sampling : Data Model")->p1

ggplot(Sample_Data[Sample_Data$Method %in% Sampling_Methods[c(1,3)],],aes(x=X1,y=X2,color=SP))+
  geom_point()+theme_light()+scale_color_viridis_c()+
  gghighlight(Method!="Full Data")+ggtitle("Optimal Sampling : Data Model")->p2

ggplot(Sample_Data[Sample_Data$Method %in% Sampling_Methods[c(1,4)],],aes(x=X1,y=X2,color=SP))+
  geom_point()+theme_light()+scale_color_viridis_c()+
  gghighlight(Method!="Full Data")+ggtitle("Optimal Sampling : Assumed Model 1")->p3

ggplot(Sample_Data[Sample_Data$Method %in% Sampling_Methods[c(1,5)],],aes(x=X1,y=X2,color=SP))+
  geom_point()+theme_light()+scale_color_viridis_c()+
  gghighlight(Method!="Full Data")+ggtitle("Optimal Sampling : Assumed Model 2")->p4

ggplot(Sample_Data[Sample_Data$Method %in% Sampling_Methods[c(1,6)],],aes(x=X1,y=X2,color=SP))+
  geom_point()+theme_light()+scale_color_viridis_c()+
  gghighlight(Method!="Full Data")+ggtitle("Optimal Sampling : Complex Model")->p5

ggplot(Sample_Data[Sample_Data$Method %in% Sampling_Methods[c(1,7)],],aes(x=X1,y=X2,color=SP))+
  geom_point()+theme_light()+scale_color_viridis_c()+
  gghighlight(Method!="Full Data")+ggtitle("Model Robust Optimal Sampling : Data Model")->p6

ggarrange(p1,p2,p3,p4,p5,p6,nrow = 2,ncol=3,legend = "right")
ggsave("Full_Data.jpg",width = 3*8,height = 2*6)